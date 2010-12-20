//////////////////////////////////////////////////////////////////////
//
// Algebraic Decision Diagram Package (Tabular representation)
//
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
// TODO:
// -----
//
//////////////////////////////////////////////////////////////////////

package logic.add;

import graph.Graph;

import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

/**
 * Implementation of tabular representation
 **/
public class Table extends DD {

	public static Boolean TRUE = new Boolean(true);
	public static Boolean FALSE = new Boolean(false);

	public int _nRoot;
	public int _nLocalIDCnt;
	public HashMap _hmTableMap; // Integer(id) -> Class T(double[])
	public ArrayList _alEvalVars; // Just a list of the indices from [0.._alOrder.size()-1]

	//////////////////////////////////////////////////////////////////
	//                         Constructors
	//////////////////////////////////////////////////////////////////

	public Table(ArrayList order) {

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

	public Table(Table src) {

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
		return new Table(this);
	}

	public int copy(Table src, int id) {
		int new_id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(new_id), new T((T) src._hmTableMap
				.get(new ADDRNode(id))));
		return new_id;
	}

	public void setRoot(int id) {
		_nRoot = id;
	}

	//////////////////////////////////////////////////////////////////
	//                  Node Maintenance and Flushing
	//////////////////////////////////////////////////////////////////

	// Flush caches but save special nodes.  
	public void flushCaches(boolean print_info) {

		// Print starting info
		if (print_info) {
			System.out.print("[FLUSHING CACHES... ");
			//showCacheSize();
			ResetTimer();
		}

		//System.out.println("Flushing: " + _hmTableMap.keySet() + 
		//		   " not in " + _hsSpecialNodes);
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

		// Relevant vars here are PRUNE_TYPE and PRUNE_PRECISION
		if (PRUNE_TYPE == NO_REPLACE || PRUNE_PRECISION <= 0d)
			return id;

		if (PRUNE_TYPE != REPLACE_AVG) {
			System.out.println("Illegal Table replacement type " + PRUNE_TYPE);
			System.exit(1);
		}

		// Sum out each variable and compare the error of the
		// result
		double cur_allow_err = PRUNE_PRECISION;
		while (this.countExactNodes(id) > 1 && cur_allow_err > 0d) {

			// Get list of variables for current table 'id' (which changes with iterations)
			T t = new T((T) _hmTableMap.get(new ADDRNode(id)));
			Iterator i = t._alVars.iterator();
			double min_err = Double.MAX_VALUE;
			int best_var_err = -1;
			int best_table = -1;
			while (i.hasNext()) {

				// Table variables are stored with index of var, not actual var!
				Integer var = (Integer) i.next();
				Integer var_id = (Integer) _alOrder.get(var.intValue());
				//System.out.println("Testing: " + var_id);
				int sum_out = this.scalarMultiply(this.opOut(id, var_id,
						ARITH_SUM), 0.5d);
				int diff = this.applyInt(id, sum_out, ARITH_MINUS);
				double cur_err = Math.max(Math.abs(this.getMinValue(diff)),
						Math.abs(this.getMaxValue(diff)));
				//System.out.println("  error = " + cur_err);
				if (cur_err < min_err) {
					min_err = cur_err;
					best_var_err = var_id;
					best_table = sum_out;
				}
			}
			if (min_err <= cur_allow_err) {
				id = best_table;
				cur_allow_err = cur_allow_err - min_err;
				//System.out.println("Pruning: " + best_var_err);
				//System.out.println(" => \n" + printNode(id)); 
			} else {
				return id; // No elimination suffices, so return as is
			}
		}

		return id;
	}

	//////////////////////////////////////////////////////////////////
	//           Construction / Application / Evaluation
	//////////////////////////////////////////////////////////////////

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

	// Copy data from a DD to a new Table, apply restriction op
	// to gid if not -1.
	public T copyFrom(DD other, int id, int gid, int op) {

		// Note: evaluate only looks at relevant eval_var_setting
		//       so only need to modify the relevant ones

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
					System.out.println("Table.T.copyFrom: Invalid restriction");
					System.exit(1);
				}
			} else {
				System.err
						.println("Table.T.copyFrom: GID index not found for restriction");
				System.err
						.println("Continuing, but probably erroneous output.");
			}
		}

		// Now, copy over
		T table = new T(vars);
		//System.out.println("GID: " + gid_index + "  OP: " + 
		//                   op + "  Vars: " + table._alVars);
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
			table.set(table._settings, other.evaluate(id, eval_var_setting));
		}

		return table;
	}

	// Internal and external Apply
	public int applyInt(int a1, int a2, int op) {

		//System.out.println(_hmTableMap);
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
				tr.set(settings, (t1.projectAndEval(new_vars, settings) + t2
						.projectAndEval(new_vars, settings)));
			}
		}
			break;
		case ARITH_PROD: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				tr.set(settings, (t1.projectAndEval(new_vars, settings) * t2
						.projectAndEval(new_vars, settings)));
			}
		}
			break;
		case ARITH_MIN: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				tr.set(settings, (Math.min(t1
						.projectAndEval(new_vars, settings), t2.projectAndEval(
						new_vars, settings))));
			}
		}
			break;
		case ARITH_MAX: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				tr.set(settings, (Math.max(t1
						.projectAndEval(new_vars, settings), t2.projectAndEval(
						new_vars, settings))));
			}
		}
			break;
		case ARITH_DIV: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				tr.set(settings, (t1.projectAndEval(new_vars, settings) / t2
						.projectAndEval(new_vars, settings)));
			}
		}
			break;
		case ARITH_MINUS: {
			for (int i = 0; i < entries; i++) {
				for (int j = 0; j < nvars; j++) {
					settings.set(j, (((i >> (nvars - j - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}
				tr.set(settings, (t1.projectAndEval(new_vars, settings) - t2
						.projectAndEval(new_vars, settings)));
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
		T t = new T((T) _hmTableMap.get(new ADDRNode(rid)));
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

		return id;
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
		return applyInt(id_low, id_high, op);
	}

	// For restricting a variable
	public int restrict(int rid, int gid, int op) {

		if (op != RESTRICT_HIGH && op != RESTRICT_LOW) {
			System.out
					.println("ERROR: opOut called without RESTRICT_{HIGH/LOW}");
			Object o = null;
			o.toString();
		}

		// Build a new table via evaluation, setting the restricted
		// var to it's appropriate setting
		int new_id = _nLocalIDCnt++;
		_hmTableMap.put(new ADDRNode(new_id), copyFrom(this, rid, gid, op));
		return new_id;
	}

	//////////////////////////////////////////////////////////////////
	//                    Arithmetic Operations
	//////////////////////////////////////////////////////////////////

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

		int new_id = _nLocalIDCnt++;
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		T new_t = new T(t._alVars);
		_hmTableMap.put(new ADDRNode(new_id), new_t);
		double[] darray_src = t._darray;
		double[] darray_dest = new_t._darray;
		int entries = 1 << t._sz;
		for (int i = 0; i < entries; i++) {
			darray_dest[i] = darray_src[i] * val;
		}
		return new_id;
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

		int new_id = _nLocalIDCnt++;
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		T new_t = new T(t._alVars);
		_hmTableMap.put(new ADDRNode(new_id), new_t);
		double[] darray_src = t._darray;
		double[] darray_dest = new_t._darray;
		int entries = 1 << t._sz;
		for (int i = 0; i < entries; i++) {
			darray_dest[i] = 1d / darray_src[i];
		}
		return new_id;
	}

	public int negate(int id) { // -DD

		int new_id = _nLocalIDCnt++;
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		T new_t = new T(t._alVars);
		_hmTableMap.put(new ADDRNode(new_id), new_t);
		double[] darray_src = t._darray;
		double[] darray_dest = new_t._darray;
		int entries = 1 << t._sz;
		for (int i = 0; i < entries; i++) {
			darray_dest[i] = -darray_src[i];
		}
		return new_id;
	}

	//////////////////////////////////////////////////////////////////
	//                     Internal Statistics
	//////////////////////////////////////////////////////////////////

	// Quick cache snapshot
	public void showCacheSize() {
		System.out.println("Table requires no cache");
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

	//////////////////////////////////////////////////////////////////
	//                   Printing and Comparison
	//////////////////////////////////////////////////////////////////

	// Show pruning information
	public void pruneReport() {
		System.out.println("Table: no pruning");
	}

	public Graph getGraph(int id) {
		return getGraph(id, null);
	}
	
	public Graph getGraph(int id, Map id2var) {
		if (id2var != null)
			System.out.println("Error: variable remapping not implemented for 'Table'");
		Graph g = new Graph(true /* directed */, false /* bottom-to-top */,
				/*left-to-right*/ false, true /* multi-links */);

		g.addNode("t");
		T t = (T) _hmTableMap.get(new ADDRNode(id));
		g.addNodeShape("t", "record");
		g.addNodeLabel("t", t.toGVizRecord());

		return g;
	}

	// Print out a node
	public String printNode(int id) {

		T t = (T) _hmTableMap.get(new ADDRNode(id));
		return t.toString();
	}

	//////////////////////////////////////////////////////////////////
	//                     Inner Table Class
	//////////////////////////////////////////////////////////////////

	// The relation between _alOrder in Table and _alVars in T can
	// be confusing and is explained here with an example:
	//
	// _alOrder: index   0  1  2  3   4  5
	//           value [ 5  4  7  9  11  0 ] <- i.e., var ids
	//
	// _alVars: (subset of vars in _alOrder, refers to _alOrder *index*)
	//           index   0    1    2    3 
	//           value [ 0    2    4    5 ]
	//    array offset   2^0  2^1  2^2  2^3
	//
	//         var ids   5    7   11    0    <- i.e., _alOrder.get(val)
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

		// 'vars' is the index of the variable in the global _alOrder,
		// this list should be monotonically increasing.
		public T(ArrayList vars) {
			_alVars = vars;
			_sz = vars.size();
			_entries = 1 << _sz;
			if (_sz > 30) {
				System.out
						.println("Table.T: ERROR: Size exceeds available address space");
				System.exit(1);
			}
			_darray = new double[_entries]; // 2^{#vars} entries

			// Initialize settings array (to be reused)
			_settings = new ArrayList();
			for (int i = 0; i < _sz; i++) {
				_settings.add(FALSE);
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
		}

		// Set value based on setting of variable superset
		public void projectAndSet(ArrayList supset_vars,
				ArrayList supset_setting, double val) {
			int index = 0;
			int supset_sz = supset_vars.size();
			for (int i = 0, j = 0; i < _sz && j < supset_sz;) {

				Integer vi = (Integer) _alVars.get(i);
				Integer vj = (Integer) supset_vars.get(j);
				int compare_val = ((Integer) _alVars.get(i))
						.compareTo((Integer) supset_vars.get(j));
				if (compare_val == 0) {
					// both share this var, get setting, update index, inc both i&j
					Boolean b = (Boolean) supset_setting.get(j);
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
			_darray[index] = val;
		}

		// Set value based on setting of exact variable set
		public void set(ArrayList setting, double val) {
			int index = 0;
			for (int i = 0; i < _sz; i++) {
				Boolean b = (Boolean) setting.get(i);
				if (b.booleanValue()) {
					index += (1 << i);
				}
			}
			_darray[index] = val;
		}

		// Eval based on setting of variable superset
		public double projectAndEval(ArrayList supset_vars,
				ArrayList supset_setting) {

			int index = 0;
			int supset_sz = supset_vars.size();
			for (int i = 0, j = 0; i < _sz && j < supset_sz;) {

				Integer vi = (Integer) _alVars.get(i);
				Integer vj = (Integer) supset_vars.get(j);
				int compare_val = ((Integer) _alVars.get(i))
						.compareTo((Integer) supset_vars.get(j));
				if (compare_val == 0) {
					// both share this var, get setting, update index, inc both i&j
					Boolean b = (Boolean) supset_setting.get(j);
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
			return _darray[index];

		}

		// Eval based on setting of exact variable set
		public double eval(ArrayList setting) {
			int index = 0;
			for (int i = 0; i < _sz; i++) {
				Boolean b = (Boolean) setting.get(i);
				if (b.booleanValue()) {
					index += (1 << i);
				}
			}
			return _darray[index];
		}

		public String toGVizRecord() {

			StringBuffer sb1 = new StringBuffer();
			StringBuffer sb2 = new StringBuffer();

			// Now print table
			sb1.append("Vars: ");
			Iterator i = _alVars.iterator();
			while (i.hasNext()) {
				sb1.append(_alOrder.get(((Integer) i.next()).intValue()) + " ");
			}
			for (int c = 0; c < _entries; c++) {

				// Set all bits
				// c >> 0 is low bit which comes last (pos 2)
				for (int b = _sz - 1; b >= 0; b--) {
					_settings.set(b, (((c >> (_sz - b - 1)) & 1) == 1) ? TRUE
							: FALSE);
				}

				// Now show the assignment
				sb1.append("|" + DD.PrintBitVector(_settings, false));
				sb2.append("|" + DD._df.format(eval(_settings)));
			}
			return "{" + sb1 + "}|{" + sb2 + "}";

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
				sb.append("Assignment: " + DD.PrintBitVector(_settings)
						+ " -> " + DD._df.format(eval(_settings)) + "\n");
			}
			return sb.toString();
		}
	}
}
