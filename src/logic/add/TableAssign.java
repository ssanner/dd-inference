//////////////////////////////////////////////////////////////////////
//
// Algebraic Decision Diagram Package (Tabular representation)
//
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
// TODO:
// -----
// Note: This version tracks assignments for variable elimination.
//       Should merge with Table. 
//////////////////////////////////////////////////////////////////////

package logic.add;

import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

import graph.Graph;
import util.*;

/**
 * Implementation of tabular representation
 */
public class TableAssign extends DD {

	public static Boolean TRUE = new Boolean(true);
	public static Boolean FALSE = new Boolean(false);
	public int _nRoot;
	public int _nLocalIDCnt;
	public HashMap _hmTableMap; // Integer(id) -> Class T(double[])
	public ArrayList _alEvalVars; // Just a list of the indices from
								  // [0.._alOrder.size()-1]
    
    // For maintaining max/min assignment during elimination
    // TODO: Might want to make non-static! 
    public static boolean MAINTAIN_ASSIGN = false;
    public static boolean MAINTAIN_COEF = false;

	// ////////////////////////////////////////////////////////////////
	// Constructors
	// ////////////////////////////////////////////////////////////////

	public TableAssign(ArrayList order) {

		_nLocalIDCnt = 0;
		_nRoot = INVALID;
		_alOrder = (ArrayList) order.clone();
		_hmTableMap = new HashMap();
		_hmGVarToLevel = new HashMap();

		// Initialize indices array (to be used during eval)
		_alEvalVars = new ArrayList();
		for (int i = 0; i < _alOrder.size(); i++) {
			_alEvalVars.add(new Integer(i));
		}

		// Build map from global var to order level
		_hmGVarToLevel.clear();
		for (int i = 0; i < _alOrder.size(); i++) {
			_hmGVarToLevel.put((Integer) _alOrder.get(i), new Integer(i));
		}
	}

	public TableAssign(TableAssign src) {

		_nLocalIDCnt = 0;
		_hmTableMap = new HashMap();

		// Takes care of root, order, gvar_map, nodeLevel
		_alOrder = (ArrayList) src._alOrder.clone();
		_hmGVarToLevel = (HashMap) src._hmGVarToLevel.clone();

		// Initialize indices array (to be used during eval)
		_alEvalVars = new ArrayList();
		for (int i = 0; i < _alOrder.size(); i++) {
			_alEvalVars.add(new Integer(i));
		}

		// Copy over the node structure and load the caches
		setRoot(copy(src, src._nRoot));
	}

	public Object clone() {
		return new TableAssign(this);
	}

	public int copy(TableAssign src, int id) {
		int new_id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(new_id), new T((T) src._hmTableMap
				.get(new ADDRNode(id))));
		return new_id;
	}

	public void setRoot(int id) {
		_nRoot = id;
	}

	// ////////////////////////////////////////////////////////////////
	// Maintaining MAX / MIN assignments
	// ////////////////////////////////////////////////////////////////

	public static boolean MergeAssignment(IntArray target, int gid, boolean high) {
		int loc = -1;
		if ((loc = target.find(gid)) != -1) {
			return target.l[loc + 1] == (high ? 1 : 0);
		} else {
			target.add(gid);
			target.add(high ? 1 : 0);
			return true;
		}
	}

	public static boolean MergeAssignments(IntArray target, IntArray assign) {
		for (int i = 0; i < assign.count; i+=2) {
			//System.out.println("Merging assignment: " + assign.l[i] + " -> " + (assign.l[i+1] == 1) + " into " + target);
			if (!MergeAssignment(target, assign.l[i], assign.l[i+1] == 1))
				return false;
		}
		return true;
	}
	
	// ////////////////////////////////////////////////////////////////
	// Node Maintenance and Flushing
	// ////////////////////////////////////////////////////////////////

	// Flush caches but save special nodes.
	public void flushCaches(boolean print_info) {

		// Print starting info
		if (print_info) {
			System.out.print("[FLUSHING CACHES... ");
			// showCacheSize();
			ResetTimer();
		}

		// System.out.println("Flushing: " + _hmTableMap.keySet() +
		// " not in " + _hsSpecialNodes);
		Iterator i = (new HashSet((Set) _hmTableMap.keySet())).iterator();
		while (i.hasNext()) {
			ADDRNode id_ref = (ADDRNode) i.next();
			if (!_hsSpecialNodes.contains(id_ref)) {
				_hmTableMap.remove(id_ref); // Let Java GC do the rest
			}
		}

		// Print results
		if (GC_DURING_FLUSH) {
			RUNTIME.gc();
		}
		if (print_info) {
			System.out.print(" TIME: " + GetElapsedTime());
			System.out
					.print("  RESULT: "
							+ _df
									.format(((double) RUNTIME.freeMemory() / (double) RUNTIME
											.totalMemory())));
			System.out.print("  CACHE: " + getCacheSize() + "] ");
		}
	}

	// Pruning not implemented for table
	public int pruneNodes(int id) {
		System.out.println("Pruning not enabled for TableAssign... copy code from Table.java");
		return id;
	}
	
	public Graph getGraph(int id) {
		return getGraph(id, null);
	}
	
	public Graph getGraph(int id, Map id2var) {
		if (id2var != null)
			System.out.println("Error: variable remapping not implemented for 'TableAssign'");
		System.out.println("Graph drawing not enabled for TableAssign... copy code from Table.java");
		return null;
	}
	
	// ////////////////////////////////////////////////////////////////
	// Construction / Application / Evaluation
	// ////////////////////////////////////////////////////////////////

	// Build a var ADD
	public int getVarNode(int gid, double low, double high) {
		ArrayList vars = new ArrayList();
		vars.add(_hmGVarToLevel.get(new Integer(gid)));
		T table = new T(vars);
		ArrayList setting = new ArrayList();
		setting.add(new Boolean(false));
		table.set(setting, low);
		setting.set(0, new Boolean(true));
		table.set(setting, high);
		int id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(id), table);
		return id;
	}

	// Build a constant ADD
	public int getConstantNode(double val) {
		ArrayList empty = new ArrayList();
		T table = new T(empty);
		table.set(empty, val);
		int id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(id), table);
		return id;
	}

	// Build an ADD from a list (node is a list, high comes first for
	// internal nodes)
	public int buildDDFromUnorderedTree(ArrayList l, Map var2ID) {
		DD tmp = new ADD(_alOrder);
		int id = tmp.buildDDFromUnorderedTree(l, var2ID);
		int new_id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(new_id), copyFrom(tmp, id, -1, -1));
		return new_id;
	}

	// Build an ADD from a list with correct variable order (node is a
	// list, high comes first for internal nodes)
	public int buildDDFromOrderedTree(ArrayList l, Map var2ID) {
		DD tmp = new ADD(_alOrder);
		int id = tmp.buildDDFromOrderedTree(l, var2ID);
		int new_id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(new_id), copyFrom(tmp, id, -1, -1));
		return new_id;
	}

	// Copy data from a DD to a new TableOld, apply restriction op
	// to gid if not -1.
	// TODO: This could be an inefficient approach.
	public T copyFrom(DD other, int id, int gid, int op) {

		// Note: evaluate only looks at relevant eval_var_setting
		// so only need to modify the relevant ones

		// Collect gids from DD to initialize new table
		ArrayList eval_var_setting = new ArrayList();
		int gid_index = -1;
		Set gids = other.getGIDs(id);
		ArrayList vars = new ArrayList();
		for (int i = 0; i < _alOrder.size(); i++) {
			Integer var_id;
			if (gids.contains(var_id = (Integer) _alOrder.get(i))) {
				if (var_id.intValue() == gid) {
					gid_index = i;
				} else {
					// Don't add index to var set if restricted
					vars.add(new Integer(i));
				}
			}
			eval_var_setting.add(FALSE);
		}

		// Get index of gid in alOrder and set eval_setting
		if (gid != -1) {
			if (gid_index >= 0) {
				if (op == RESTRICT_HIGH) {
					eval_var_setting.set(gid_index, TRUE);
				} else if (op == RESTRICT_LOW) {
					eval_var_setting.set(gid_index, FALSE);
				} else {
					System.out.println("TableOld.T.copyFrom: Invalid restriction");
					System.exit(1);
				}
			} else {
				System.err.println("TableOld.T.copyFrom: GID index " + gid + " +not found for restriction");
				System.err.println(this.printNode(id));
				System.err.println("Continuing, but probably erroneous output.");
				Object o = null; o.toString();
			}
		}

		// Now, copy over
		T table = new T(vars);
		// System.out.println("GID: " + gid_index + " OP: " +
		// op + " Vars: " + table._alVars);
		for (int c = 0; c < table._entries; c++) {

			// Set all bits
			// c >> 0 is low bit which comes last (pos 2)
			for (int b = table._sz - 1; b >= 0; b--) {
				Boolean bset = (((c >> (table._sz - b - 1)) & 1) == 1) ? TRUE
						: FALSE;
				table._settings.set(b, bset);
				eval_var_setting.set(((Integer) table._alVars.get(b))
						.intValue(), bset);
			}

            // Now evaluate the DD and set the table for this entry
			if (other instanceof TableAssign) {
				
				int table_index = table.getFullIndex(table._settings);
				T other_table = (T)((TableAssign)other)._hmTableMap.get(new ADDRNode(id));
				int other_index = other_table.getProjectedIndex(((TableAssign)other)._alEvalVars, eval_var_setting);
				table._darray[table_index] = other_table._darray[other_index]; 
				
				if (MAINTAIN_ASSIGN)
					MergeAssignments(table._aAssignments[table_index], other_table._aAssignments[other_index]); 
				
			} else
				table.set( table._settings, other.evaluate(id, eval_var_setting) );
		}

		return table;
	}

	// Internal and external Apply
	public int applyInt(int a1, int a2, int op) {

		// System.out.println(_hmTableMap);
		T t1 = (T) _hmTableMap.get(new ADDRNode(a1));
		T t2 = (T) _hmTableMap.get(new ADDRNode(a2));
		ArrayList new_vars = MergeSortedLists(t1._alVars, t2._alVars);
		T tr = new T(new_vars);
		int id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(id), tr);
		ArrayList settings = tr._settings;
		int nvars = new_vars.size();
		int entries = 1 << nvars;

		switch (op) {
		case ARITH_SUM: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				
				// Compute indexes into tables and set results
				int t1_index = t1.getProjectedIndex(new_vars, settings);
				int t2_index = t2.getProjectedIndex(new_vars, settings);
				int tr_index = tr.getFullIndex(settings);
				tr._darray[tr_index] = t1._darray[t1_index] + t2._darray[t2_index];
				
				// ASSIGN
				if (MAINTAIN_ASSIGN) {
					if (!MergeAssignments(tr._aAssignments[tr_index], t1._aAssignments[t1_index])) 
						System.out.println("Merge error during SUM");
					if (!MergeAssignments(tr._aAssignments[tr_index], t2._aAssignments[t2_index]))
						System.out.println("Merge error during SUM");
				}
				
				// COEFFICIENTS
				if (MAINTAIN_COEF) {
					AddInCoefs(tr._hmCoef[tr_index], t1._hmCoef[t1_index], false /*subtract*/);
					AddInCoefs(tr._hmCoef[tr_index], t2._hmCoef[t2_index], false /*subtract*/);
				}
			}
		}
			break;
		case ARITH_PROD: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				
				// Compute indexes into tables and set results
				int t1_index = t1.getProjectedIndex(new_vars, settings);
				int t2_index = t2.getProjectedIndex(new_vars, settings);
				int tr_index = tr.getFullIndex(settings);
				tr._darray[tr_index] = t1._darray[t1_index] * t2._darray[t2_index];
				
				// ASSIGN
				if (MAINTAIN_ASSIGN) {
					if (!MergeAssignments(tr._aAssignments[tr_index], t1._aAssignments[t1_index])) 
						System.out.println("Merge error during PROD");
					if (!MergeAssignments(tr._aAssignments[tr_index], t2._aAssignments[t2_index]))
						System.out.println("Merge error during PROD");
				}
								
				// COEFFICIENTS
				if (MAINTAIN_COEF) {
					
					// Check that only one table has coefs, swap as necessary
					boolean t1_has_coefs = t1._hmCoef[t1_index].size() != 0; 
					if (t1_has_coefs && t2._hmCoef[t2_index].size() != 0) {
						System.out.println("Error: both t1 and t2 have coefficients, cannot multiply!");
					}
					
					if (t1_has_coefs) {
						tr._hmCoef[tr_index] = ScalarMultiplyCoefs(t2._darray[t2_index], t1._hmCoef[t1_index]);
					} else {
						tr._hmCoef[tr_index] = ScalarMultiplyCoefs(t1._darray[t1_index], t2._hmCoef[t2_index]);
					}	
				}

			}
		}
			break;
		case ARITH_MIN: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				
				// Compute indexes into tables and set results
				int t1_index = t1.getProjectedIndex(new_vars, settings);
				int t2_index = t2.getProjectedIndex(new_vars, settings);
				int tr_index = tr.getFullIndex(settings);
				double t1_val = t1._darray[t1_index];
				double t2_val = t2._darray[t2_index];
				boolean lhs_val = t1_val <= t2_val;
				tr._darray[tr_index] = lhs_val ? t1_val : t2_val;
				
				// ASSIGN
				if (MAINTAIN_ASSIGN) {
					if (!MergeAssignments(tr._aAssignments[tr_index], lhs_val ? t1._aAssignments[t1_index] : t2._aAssignments[t2_index]))
						System.out.println("Merge error during MIN");
				}
			}
		}
			break;
		case ARITH_MAX: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				
				// Compute indexes into tables and set results
				int t1_index = t1.getProjectedIndex(new_vars, settings);
				int t2_index = t2.getProjectedIndex(new_vars, settings);
				int tr_index = tr.getFullIndex(settings);
				double t1_val = t1._darray[t1_index];
				double t2_val = t2._darray[t2_index];
				boolean lhs_val = t1_val >= t2_val;
				tr._darray[tr_index] = lhs_val ? t1_val : t2_val;
				
				// ASSIGN
				if (MAINTAIN_ASSIGN) {
					if (!MergeAssignments(tr._aAssignments[tr_index], lhs_val ? t1._aAssignments[t1_index] : t2._aAssignments[t2_index]))
						System.out.println("Merge error during MAX");
				}
			}
		}
			break;
		case ARITH_DIV: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				
				// Compute indexes into tables and set results
				int t1_index = t1.getProjectedIndex(new_vars, settings);
				int t2_index = t2.getProjectedIndex(new_vars, settings);
				int tr_index = tr.getFullIndex(settings);
				tr._darray[tr_index] = t1._darray[t1_index] / t2._darray[t2_index];
				
				// ASSIGN
				if (MAINTAIN_ASSIGN) {
					if (!MergeAssignments(tr._aAssignments[tr_index], t1._aAssignments[t1_index])) 
						System.out.println("Merge error during DIV");
					if (!MergeAssignments(tr._aAssignments[tr_index], t2._aAssignments[t2_index]))
						System.out.println("Merge error during DIV");
				}
				
				if (MAINTAIN_COEF && t2._hmCoef[t2_index].size() != 0) {
					System.out.println("Divisor cannot have linear coefficients.");
					System.exit(1);
				}
				  
			}
		}
			break;
		case ARITH_MINUS: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				
				// Compute indexes into tables and set results
				int t1_index = t1.getProjectedIndex(new_vars, settings);
				int t2_index = t2.getProjectedIndex(new_vars, settings);
				int tr_index = tr.getFullIndex(settings);
				tr._darray[tr_index] = t1._darray[t1_index] - t2._darray[t2_index];
				
				// ASSIGN
				if (MAINTAIN_ASSIGN) {
					if (!MergeAssignments(tr._aAssignments[tr_index], t1._aAssignments[t1_index])) 
						System.out.println("Merge error during MINUS");
					if (!MergeAssignments(tr._aAssignments[tr_index], t2._aAssignments[t2_index]))
						System.out.println("Merge error during MINUS");
				}
								
				// COEFFICIENTS
				if (MAINTAIN_COEF) {
					AddInCoefs(tr._hmCoef[tr_index], t1._hmCoef[t1_index], false /*subtract*/);
					AddInCoefs(tr._hmCoef[tr_index], t2._hmCoef[t2_index], true /*subtract*/);
				}
			}
		}
		break;
		default: {
			System.out.println("Invalid operator: " + op);
			System.exit(1);
		}
		}
		return id;
	}

	// Merge sort runs in linear time
	public static ArrayList MergeSortedLists(ArrayList li, ArrayList lj) {
		ArrayList ret = new ArrayList();
		int i = 0;
		int j = 0;
		int sz_i = li.size();
		int sz_j = lj.size();
		while (i < sz_i && j < sz_j) {
			Integer vi = (Integer) li.get(i);
			Integer vj = (Integer) lj.get(j);
			int compare_val = vi.compareTo(vj);
			if (compare_val == 0) {
				// Same
				ret.add(vi);
				i++;
				j++;
			} else if (compare_val < 0) {
				// vi comes before vj
				ret.add(vi);
				i++;
			} else {
				// vj comes before vi
				ret.add(vj);
				j++;
			}
		}
		while (i < sz_i) {
			ret.add(li.get(i++));
		}
		while (j < sz_j) {
			ret.add(lj.get(j++));
		}
		return ret;
	}

	// Evaluate a DD: gid == val[assign_index] -> true/false
	public double evaluate(int id, ArrayList assign) {

		T t = (T) _hmTableMap.get(new ADDRNode(id));
		return t.projectAndEval(_alEvalVars, assign);

	}

	// Remap gids... gid_map = old_id -> new_id (assuming order consistent)
	public int remapGIDsInt(int rid, HashMap gid_map) {
		int id = _nLocalIDCnt++;
		T old_table = (T) _hmTableMap.get(new ADDRNode(rid));
		T t = new T(old_table);
		_hmTableMap.put(new ADDRNode(id), t);

		// Now, just remap ids in the table
		ArrayList new_vars = new ArrayList();
		Iterator i = t._alVars.iterator();
		while (i.hasNext()) {
			Integer var = (Integer) i.next();
			Integer var_gid = (Integer) _alOrder.get(var.intValue());
			Integer remap = null;
			Integer remap_gid = null;
			if ((remap_gid = (Integer) gid_map.get(var_gid)) == null) {
				remap = var;
			} else {
				remap = (Integer) _hmGVarToLevel.get(remap_gid);
			}
			new_vars.add(remap);
		}
		t._alVars = new_vars;

		if (MAINTAIN_ASSIGN) {
			for (int j = 0; j < t._entries; j++) {
				RenameAssignments(t._aAssignments[j], gid_map);
			}
		}
		
		if (MAINTAIN_COEF) {
			for (int j = 0; j < t._entries; j++) {
				for (Object o : gid_map.entrySet()) {
					Map.Entry m = (Map.Entry)o;
					Integer var_gid = (Integer)m.getKey();
					Integer remap_gid = (Integer)m.getValue();
					Double val;
					if ((val = (Double)t._hmCoef[j].get(var_gid)) != null) {
						t._hmCoef[j].remove(var_gid);
						t._hmCoef[j].put(remap_gid, val);
					} 
				}
			}
		}
		
		return id;
	}

	public static void RenameAssignments(IntArray a, HashMap gid_map) {
		for (int i = 0; i < a.count; i+=2) {
			Integer var_gid = new Integer(a.l[i]);
			Integer remap_gid = null;
			if ((remap_gid = (Integer) gid_map.get(var_gid)) != null) {
				a.l[i] = remap_gid.intValue();
			}
		}
	}
	
	// For marginalizing out a node via sum, prod, max, or min.
	public int opOut(int rid, int gid, int op) {

		if (op != ARITH_SUM && op != ARITH_PROD && op != ARITH_MAX
				&& op != ARITH_MIN) {
			System.out.println("ERROR: opOut called without SUM/PROD/MIN/MAX");
			Object o = null;
			o.toString();
		}

		// Restrict twice and apply op
		int id_low = restrict(rid, gid, RESTRICT_LOW);
		int id_high = restrict(rid, gid, RESTRICT_HIGH);
		int ret = applyInt(id_high, id_low, op);

		return ret;
	}

	// For restricting a variable
	public int restrict(int rid, int gid, int op) {

		if (op != RESTRICT_HIGH && op != RESTRICT_LOW) {
			System.out.println("ERROR: opOut called without RESTRICT_{HIGH/LOW}");
			Object o = null;
			o.toString();
		}

		// Build a new table via evaluation, setting the restricted
		// var to it's appropriate setting
		int new_id = _nLocalIDCnt++;
		T table_r = copyFrom(this, rid, gid, op);
		if (MAINTAIN_ASSIGN)
			for (int i = 0; i < table_r._entries; i++)
				MergeAssignment(table_r._aAssignments[i], gid, op == RESTRICT_HIGH);
			
		_hmTableMap.put(new ADDRNode(new_id), table_r);
		return new_id;
	}

	// ////////////////////////////////////////////////////////////////
	// Arithmetic Operations
	// ////////////////////////////////////////////////////////////////

	// Arithmetic operations
	public double getMinValue(int id) {
		double min = Double.POSITIVE_INFINITY;
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		double[] darray = t._darray;
		int entries = 1 << t._sz;
		for (int i = 0; i < entries; i++) {
			if (darray[i] < min) {
				min = darray[i];
			}
		}
		return min;
	}

	public double getMaxValue(int id) {
		double max = Double.NEGATIVE_INFINITY;
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		double[] darray = t._darray;
		int entries = 1 << t._sz;
		for (int i = 0; i < entries; i++) {
			if (darray[i] > max) {
				max = darray[i];
			}
		}
		return max;
	}

	public int scalarMultiply(int id, double val) {
		int mult = getConstantNode(val);
		return applyInt(mult, id, ARITH_PROD);
	}

	public int scalarAdd(int id, double val) {

		int new_id = _nLocalIDCnt++;
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		T new_t = new T(t._alVars);
		_hmTableMap.put(new ADDRNode(new_id), new_t);
		double[] darray_src = t._darray;
		double[] darray_dest = new_t._darray;
		int entries = 1 << t._sz;
		for (int i = 0; i < entries; i++) {
			darray_dest[i] = darray_src[i] + val;
		}
		return new_id;
	}

	public int invert(int id) { // 1/DD
		int one = getConstantNode(1d);
		return applyInt(one, id, ARITH_DIV);
	}

	public int negate(int id) { // -DD
		int zero = getConstantNode(0d);
		return applyInt(zero, id, ARITH_MINUS);
	}

	// ////////////////////////////////////////////////////////////////
	// Internal Statistics
	// ////////////////////////////////////////////////////////////////

	// Quick cache snapshot
	public void showCacheSize() {
		System.out.println("TableOld requires no cache");
	}

	// Total cache snapshot
	public long getCacheSize() {
		long count = 0;
		Iterator i = _hsSpecialNodes.iterator();
		while (i.hasNext()) {
			count += ((T) _hmTableMap.get((ADDRNode) i.next()))._entries;
		}
		return count;
	}

	// An exact count for the ADD rooted at _nRoot
	public long countExactNodes(int id) {
		return ((T) _hmTableMap.get(new ADDRNode(id)))._entries;
	}

	// Set of the actual node ids
	public Set getExactNodes(int id) {
		return new HashSet(); // We really don't want to return all values!
	}

	// Set of the actual variable ids used
	public Set getGIDs(int id) {
		Set s = new HashSet();
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		Iterator i = t._alVars.iterator();
		while (i.hasNext()) {
			s.add(_alOrder.get(((Integer) i.next()).intValue()));
		}
		return s;
	}
	
	// ////////////////////////////////////////////////////////////////
	// Printing and Comparison
	// ////////////////////////////////////////////////////////////////

	// Show pruning information
	public void pruneReport() {
		System.out.println("TableOld: no pruning");
	}

	// Print out a node
	public String printNode(int id) {

		T t = (T) _hmTableMap.get(new ADDRNode(id));
		return t.toString();
	}

	// ////////////////////////////////////////////////////////////////
	// Coefficient Computation
	// ////////////////////////////////////////////////////////////////
	
	// TODO: Finish up impl of methods, finish applyInt, updateMapGIDs
	public static void AddInCoefs(HashMap dst, HashMap coef, boolean subtract) {
		for (Object o : coef.entrySet()) {
			Map.Entry m = (Map.Entry)o;
			Integer key = (Integer)m.getKey();
			Double val1 = (Double)m.getValue();
			if (subtract) val1 = -val1;
			Double val2 = null;
			if ((val2 = (Double)dst.get(key)) != null) {
				double new_val = val1.doubleValue() + val2.doubleValue();
				dst.put(key, new Double(new_val));
			} else {
				dst.put(key, val1);
			}
		}
	}
	
    public static HashMap ScalarMultiplyCoefs(double val, HashMap coefs) {
		HashMap new_coefs = new HashMap();
		for (Object o : coefs.entrySet()) {
			Map.Entry m = (Map.Entry)o;
			Integer key = (Integer)m.getKey();
			double val_new = val * ((Double)m.getValue()).doubleValue();
			if (val_new != 0d) new_coefs.put(key, new Double(val_new));
		}
		return new_coefs;
    }
		
	public void setCoefficient(int rid, int var_id, double val) {
		T t = (T) _hmTableMap.get(new ADDRNode(rid));
		t.setCoefficient(var_id, val);
	}

    public int instantiate(int rid, HashMap var_val) {
		int new_id = _nLocalIDCnt++;
		T cur_t = (T) _hmTableMap.get(new ADDRNode(rid));
		T new_t = new T(cur_t);
		_hmTableMap.put(new ADDRNode(new_id), new_t);
		new_t.instantiate(var_val);
		return new_id;
    }
    
	// ////////////////////////////////////////////////////////////////
	// Inner TableOld Class
	// ////////////////////////////////////////////////////////////////

	// The relation between _alOrder in TableOld and _alVars in T can
	// be confusing and is explained here with an example:
	//
	// _alOrder: index 0 1 2 3 4 5
	// value [ 5 4 7 9 11 0 ] <- i.e., var ids
	//
	// _alVars: (subset of vars in _alOrder, refers to _alOrder *index*)
	// index 0 1 2 3
	// value [ 0 2 4 5 ]
	// array offset 2^0 2^1 2^2 2^3
	//
	// var ids 5 7 11 0 <- i.e., _alOrder.get(val)
	//
	// This setup makes projection from _alOrder -> _alVars efficient
	// for various table operations.

	// Implementation of table based on double[], immutable class
	public class T {
		
		public int _sz;
		public int _entries;
		public ArrayList _alVars;
		public double[] _darray;
		public ArrayList _settings;
		public IntArray[] _aAssignments;
		public HashMap[] _hmCoef; // Main lin comb, maps w_i -> coef of w_i

		// 'vars' is the index of the variable in the global _alOrder,
		// this list should be monotonically increasing.
		public T(ArrayList vars) {
			_alVars = vars;
			_sz = vars.size();
			_entries = 1 << _sz;
			if (_sz > 30) {
				System.out.println("TableOld.T: ERROR: Size exceeds available address space");
				System.exit(1);
			}
			_darray = new double[_entries]; // 2^{#vars} entries

			// Initialize settings array (to be reused)
			_settings = new ArrayList();
			for (int i = 0; i < _sz; i++) {
				_settings.add(FALSE);
			}
			
			// Allocate assignment array if needed
			if (MAINTAIN_ASSIGN) {
				if (_sz > 16) {
					System.out.println("TableOld.T: ERROR: Size exceeds available address space when maintaining max/min assignments");
					System.exit(1);
				}
				_aAssignments = new IntArray[_entries]; // 2^{#vars} entries
				for (int i = 0; i < _entries; i++)
					_aAssignments[i] = new IntArray();
			}
			
			if (MAINTAIN_COEF) { 
				if (_sz > 16) {
					System.out.println("TableOld.T: ERROR: Size exceeds available address space when maintaining coefs");
					System.exit(1);
				}
				_hmCoef = new HashMap[_entries]; // 2^{#vars} entries
				for (int i = 0; i < _entries; i++)
					_hmCoef[i] = new HashMap();

			}
		}

		public T(T src) {
			_sz = src._sz;
			_alVars = src._alVars;
			_entries = 1 << _sz;
			_darray = new double[_entries];
			System.arraycopy(src._darray, 0, _darray, 0, _entries);

			// Initialize settings array (to be reused)
			_settings = new ArrayList();
			for (int i = 0; i < _sz; i++) {
				_settings.add(FALSE);
			}
						
			// Allocate assignment array if needed
			if (MAINTAIN_ASSIGN) {
				if (_sz > 16) {
					System.out.println("TableOld.T: ERROR: Size exceeds available address space when maintaining max/min assignments");
					System.exit(1);
				}
				_aAssignments = new IntArray[_entries]; // 2^{#vars} entries
				for (int i = 0; i < _entries; i++)
					_aAssignments[i] = new IntArray(src._aAssignments[i].l, src._aAssignments[i].count);
			}
			
			if (MAINTAIN_COEF) {
				if (_sz > 16) {
					System.out.println("TableOld.T: ERROR: Size exceeds available address space when maintaining coefs");
					System.exit(1);
				}
				_hmCoef = new HashMap[_entries]; // 2^{#vars} entries
				for (int i = 0; i < _entries; i++)
					_hmCoef[i] = (HashMap)src._hmCoef[i].clone();
			}
		}

		// Get the correct index into the table for the given
		// assignment to the given vars
		public int getProjectedIndex(ArrayList supset_vars, ArrayList supset_setting) {
			int index = 0;
			int supset_sz = supset_vars.size();
			//System.out.println("ProjectIndex: Given: " + supset_vars + ", " + supset_setting);
			//System.out.println("Local Vars: " + _alVars);
			for (int i = 0, j = 0; i < _sz && j < supset_sz;) {

				Integer vi = (Integer) _alVars.get(i);
				Integer vj = (Integer) supset_vars.get(j);
				int compare_val = ((Integer) _alVars.get(i))
						.compareTo((Integer) supset_vars.get(j));
				//System.out.println("Compared: " + vi + " to " + vj);
				if (compare_val == 0) {
					// both share this var, get setting, update index, inc both
					// i&j
					Boolean b = (Boolean) supset_setting.get(j);
					//System.out.println("Setting: " + b);
					if (b.booleanValue()) {
						index += (1 << i);
					}
					i++;
					j++;
				} else if (compare_val < 0) {
					// alVars comes before supset_setting
					i++;
				} else {
					// supset_setting comes before alVars
					j++;
				}
			}
			return index;
		}
		
		// Set value based on setting of variable superset
		public void projectAndSet(ArrayList supset_vars,
				ArrayList supset_setting, double val) {
			
			int index = getProjectedIndex(supset_vars, supset_setting);
			_darray[index] = val;
		}

		// Get the correct index into the table for the given
		// assignment to *all* of the vars
		public int getFullIndex(ArrayList setting) {
			int index = 0;
			for (int i = 0; i < _sz; i++) {
				Boolean b = (Boolean) setting.get(i);
				if (b.booleanValue()) {
					index += (1 << i);
				}
			}
			return index;
		}
		
		// Set value based on setting of exact variable set
		public void set(ArrayList setting, double val) {
			int index = getFullIndex(setting);
			_darray[index] = val;
		}

		// Eval based on setting of variable superset
		public double projectAndEval(ArrayList supset_vars,
				ArrayList supset_setting) {

			int index = getProjectedIndex(supset_vars, supset_setting);
			return _darray[index];

		}

		// Eval based on setting of exact variable set
		public double eval(ArrayList setting) {
			int index = getFullIndex(setting);
			return _darray[index];
		}

		// Print as String
		public String toString() {

			StringBuffer sb = new StringBuffer();

			// Now print table
			sb.append("Vars: [ ");
			Iterator i = _alVars.iterator();
			while (i.hasNext()) {
				sb.append(_alOrder.get(((Integer) i.next()).intValue()) + " ");
			}
			sb.append("]\n");
			for (int c = 0; c < _entries; c++) {

				// Set all bits
				// c >> 0 is low bit which comes last (pos 2)
				for (int b = _sz - 1; b >= 0; b--) {
					_settings.set(b, (((c >> (_sz - b - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}

				// Now show the assignment
				int setting_index = getFullIndex(_settings);
				sb.append("Assignment: " + DD.PrintBitVector(_settings)
						+ " -> " + DD._df.format(_darray[setting_index]));
				if (MAINTAIN_COEF) 
					sb.append(", Coef: " + _hmCoef[setting_index]);
				if (MAINTAIN_ASSIGN)
					sb.append(", Assignment: " + _aAssignments[setting_index]);
				sb.append("\n");
			}
			return sb.toString();
		}
		
		public void setCoefficient(int id, double val) {
			Integer iid = new Integer(id);
			Double dval = new Double(val);
	    	for (int entry = 0; entry < _entries; entry++)
				_hmCoef[entry].put(iid, dval);
		}
	    
	    // Assume first element is for w_1, nth element is w_n
	    public void instantiate(HashMap var_val) {
	    	for (int entry = 0; entry < _entries; entry++) {
				double val = _darray[entry];
				for (Object o : var_val.entrySet()) {
					Map.Entry m = (Map.Entry)o;
					Integer var_id = (Integer)m.getKey();
					double var_assign = ((Double)m.getValue()).doubleValue();
					Double dcoef = ((Double)_hmCoef[entry].get(var_id));
					if (dcoef == null) continue;
					double coef = dcoef.doubleValue();
					val += coef * var_assign;
				}
				_darray[entry] = val;
				_hmCoef[entry].clear();
	    	}
	    }
	}
}
