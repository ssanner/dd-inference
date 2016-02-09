//////////////////////////////////////////////////////////////////////
//
	// File:     BN.java (Bayes net/decision diagram implementation)
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
// Requires: comshell package
//
// Description:
// ------------
//   An BN inference package using ADDs/AADDs in place of CPTs and
//   the variable elimination algorithm.  (More complex algorithms
//   such as junction trees could be implemented but this has not
//   been done yet.)
//
// TODO:
// -----
// - Use D-Separation
// - Make a more usable interface for Bayes net queries (see PShell)
// - Explain how to make an IR.CPT class so that anyone can
//   build another parser/BN constructor without needing to
//   understand the details of this class.  (Will need
//   common interface.)
//
//////////////////////////////////////////////////////////////////////

// Package definition
package prob.bn;

// Packages to import
import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

// For greedy tree-width computations
import graph.*;

// For DD & FRB interface
import logic.add.*;

// For parsing bif files
import prob.bn.parser.*;
import util.Pair;

/**
 * Main MDP inference class
 * 
 * @version 1.0
 * @author Scott Sanner
 * @language Java (JDK 1.3)
 **/
public class BN {

	// ///////////////////////////////////////////////////////////////////////////
	// Class Constants and Data Members
	// ///////////////////////////////////////////////////////////////////////////

	/* Local constants */
	public final static int VERBOSE = 0;

	/* For printing */
	public static DecimalFormat _df = new DecimalFormat("#.###");

	/* For cache flushing */
	public final static boolean ALWAYS_FLUSH = false;
	public final static double FLUSH_PERCENT_MINIMUM = 0.1d;

	/* Static final variables */
	public static final String SUM_OUT = "SUM_OUT";
	public static final String RESTRICT_TRUE = "RESTRICT_TRUE";
	public static final String RESTRICT_FALSE = "RESTRICT_FALSE";
	public static final String QUERY = "QUERY";

	/* Static variables */
	public static Runtime RUNTIME = Runtime.getRuntime();
	public static int ID_CNT = 0;
	public static long _lTime; // For timing purposes
	protected static Var _tempVar;
	protected static int CALLS = 0;
	
	/* The DD type to use */
	public static int DD_TYPE = -1;

	/* The context for the DD */
	public FBR _context;

	/* Local members */
	public IR _ir;

	/* File name of network */
	public String _sFilename;
	public String _sShortFilename;

	/* Tree width for current order */
	public int _nTreeWidth;

	/* Time to load */
	public long _lLoadTime;

	/* Number parent links */
	public int _nParentLinks;

	/* Total number of nodes */
	public int _nTotalNodes;

	/* List of Var */
	public HashMap _hmVarMap;

	/* Connectivity graph of nodes (forward links are to parents) */
	public Graph _graph;

	/* Var ID order for decision diagrams */
	public ArrayList _alOrder; // Var IDs
	public ArrayList _alPropOrder;

	/* Var name -> count */
	public HashMap _hmVar2Count;

	/* Var name -> value list */
	public HashMap _hmVar2Values;

	/* Var name -> CPT */
	public HashMap _hmVar2CPT;

	/* Str var (name_#) -> ID: For build DDs */
	public HashMap _hmStrVar2ID;
	public HashMap _hmID2Var;

	/* Nodes to keep from flushing */
	public ArrayList _alSaveNodes = new ArrayList();

	// ///////////////////////////////////////////////////////////////////////////
	// Constructors
	// ///////////////////////////////////////////////////////////////////////////

	/**
	 * Constructor - loads and generates a BN given a filename
	 **/
	public BN(String filename) {
		_nTotalNodes = 0;
		_nTreeWidth = -1;
		_lLoadTime = -1;
		_sFilename = filename;
		int last_slash = filename.lastIndexOf('/');
		if (last_slash < 0) {
			_sShortFilename = filename;
		} else {
			_sShortFilename = filename.substring(last_slash + 1);
		}
		_nParentLinks = 0;
		_tempVar = new Var(null, 0, -1);
		initNetwork(filename);
	}

	/**
	 * Initializate the network
	 **/
	protected void initNetwork(String filename) {

		DD.ResetTimer();

		// Read file
		try {
			_ir = new IR(new FileInputStream(filename));
		} catch (IOException e) {
			System.out.println("Exception: " + e);
			System.exit(1);
		}
		// System.out.println(_ir); // Just run parser.IR to see this

		// Next need to set up a variables
		initVariables();

		// //////////////////////////////////////////////////////////////
		// greedyTWSort is clearly the best way to go but it is time
		// consuming. Need to increase efficiency (not so much mem
		// allow). Also, a better approach would be to do greedyTWSort
		// on-line during VE to compute the best order for the query.
		//
		// But we still need to compute an DD ordering, so for quick
		// testing, topologicalSort(no rev) is a quick and typically
		// about 2X worse than the greedy sort.
		// //////////////////////////////////////////////////////////////

		// Search for an elimination ordering - get back a variable ordering
		System.out.print("\nSearching for a global sort order");
		List orig_order = _graph.greedyTWSort(true);
		_nTreeWidth = _graph._nTreeWidth;
		System.out.println("...done (TW:" + _nTreeWidth + " BV:"
				+ _df.format(_graph._dMaxBinaryWidth) + ")\n");
		_alPropOrder = new ArrayList();
		_alPropOrder.addAll(orig_order);

		// Now we need to add the binary variables (i.e. the propositions
		// above are decomposed into binary variables) in the same order.
		_alOrder = new ArrayList();
		Iterator pvars = orig_order.iterator();
		while (pvars.hasNext()) {
			String var = (String) pvars.next();
			int count = ((Integer) _hmVar2Count.get(var)).intValue();
			for (int j = 0; j < count; j++) {
				_alOrder.add(new Integer(getVar(var, j)._nID));
			}
		}

		// Now create the DD context
		_context = new FBR(DD_TYPE, _alOrder);

		// Finally need to build representations for each of the CPTs...
		// Map from original prop var heads to CPTs of binary vars.
		initCPTs();

		// Print information
		_lLoadTime = DD.GetElapsedTime();
		// System.out.println(this);
		System.out.println(printQuickStats());
	}

	/**
	 * Initialize network variables and set up the connectivity graph structure.
	 **/
	public void initVariables() {

		_hmVarMap = new HashMap();
		_hmVar2Count = new HashMap();
		_hmVar2Values = new HashMap();
		_hmStrVar2ID = new HashMap();
		_hmID2Var = new HashMap();
		_graph = new Graph();

		// For each variable
		Iterator i = _ir._network._hmVariables.entrySet().iterator();
		while (i.hasNext()) {

			IR.Variable v = (IR.Variable) ((Map.Entry) i.next()).getValue();

			// Check to see if its CPT is null
			IR.CPT ircpt = (IR.CPT) _ir._network._hmCPTs.get(v._sName);
			if (ircpt == null) {
				System.out.println(" (No CPT for: " + v._sName + ")");
				continue;
			}

			// Set number of bin vars corresponding to prop vars
			int count = v.getBinValues();
			_hmVar2Count.put(v._sName, new Integer(count));
			_graph.addNode(v._sName, count);

			// Insert all parent and child links into graph
			Iterator pi = ircpt._alParents.iterator();
			while (pi.hasNext()) {
				String par = (String) pi.next();
				_graph.addUniLink(v._sName, par);
			}

			// Get the list of String values (i.e. [HIGH, MED, LOW])
			// for this prop var
			_hmVar2Values.put(v._sName, v._alValues);

			// Generate binary variables
			for (int j = 0; j < count; j++) {
				String varname = v._sName + "_" + j;
				Var var = new Var(v._sName, j);
				_hmVarMap.put(var, var);
				_hmStrVar2ID.put(varname, new Integer(var._nID));
				_hmID2Var.put(new Integer(var._nID), var);
			}
		}
	}

	/**
	 * Build the CPT for each variable
	 **/
	public void initCPTs() {
		_hmVar2CPT = new HashMap();

		// Loop through all vars
		System.out.println("Building all CPTs...");
		Iterator i = _hmVar2Count.keySet().iterator();
		while (i.hasNext()) {

			// Get IR CPT
			String var = (String) i.next();
			IR.CPT ircpt = (IR.CPT) _ir._network._hmCPTs.get(var);
			_nParentLinks += ircpt._alParents.size();

			// Construct new Bayes net CPT (this is where the majority
			// of the CPT construction takes place).
			CPT cpt = new CPT(var, ircpt);
			_hmVar2CPT.put(var, cpt);
		}
	}

	// ///////////////////////////////////////////////////////////////////////////
	// Bayes Net Access Methods
	// ///////////////////////////////////////////////////////////////////////////

	/**
	 * Variable retrieval
	 **/
	protected Var getVar(String name, int bvar) {
		_tempVar._sName = name;
		_tempVar._bVar = bvar;
		return (Var) _hmVarMap.get(_tempVar);
	}

	protected Var getVar(Integer id) {
		return (Var) _hmID2Var.get(id);
	}

	protected List getVarsFromIDs(Collection c) {
		ArrayList new_l = new ArrayList();
		Iterator i = c.iterator();
		while (i.hasNext()) {
			new_l.add(getVar((Integer) i.next()));
		}
		return new_l;
	}

	/**
	 * Var count retrieval
	 **/
	public int getVarCount(String varname) {
		return ((Integer) _hmVar2Count.get(varname)).intValue();
	}

	public static boolean getBVarSetting(Var v, ArrayList prop_var_list,
			ArrayList assignments) {

		// Fine the correct assignment
		int index = prop_var_list.indexOf(v._sName);
		Integer val = (Integer) assignments.get(index);

		// Val should be set to correct value
		int assign = val.intValue();
		int tbvar = v._bVar;
		while (tbvar-- > 0) {
			assign >>= 1;
		}

		// System.out.println("Val: " + val + "  BVar: " +
		// v._bVar + "  Setting: " + ((assign & 1) == 1));

		return ((assign & 1) == 1);
	}

	public static boolean getBVarSetting(int bval, int assign) {

		// Val should be set to correct value
		while (bval-- > 0) {
			assign >>= 1;
		}

		return ((assign & 1) == 1);
	}

	/**
	 * Get all variables
	 **/
	public ArrayList getVariables() {
		return (ArrayList) _alPropOrder.clone();
	}

	/**
	 * All possible settings for a variable
	 **/
	public ArrayList getValues(String var) {
		return ((IR.Variable) _ir._network._hmVariables.get(var))._alValues;
	}

	/**
	 * Retrieve a list of settings for DD evaluation based on an assignment of
	 * Prop vars -> String values
	 **/
	public ArrayList assign2EvalSetting(HashMap assign) {

		Boolean TRUE = new Boolean(true);
		Boolean FALSE = new Boolean(false);

		ArrayList eval_setting = new ArrayList();
		for (int i = 0; i < _alOrder.size(); i++) {
			eval_setting.add(FALSE);
		}

		Iterator a = assign.entrySet().iterator();
		while (a.hasNext()) {

			// Get the var and its setting
			Map.Entry me = (Map.Entry) a.next();
			String var = (String) me.getKey();
			String setting = (String) me.getValue();

			// Get the assign id
			int assign_val = ((IR.Variable) _ir._network._hmVariables.get(var))._alValues
					.indexOf(setting);
			if (assign_val < 0) {
				System.out.println("Invalid var assignment: " + var + "="
						+ assign);
				System.exit(1);
			}

			// Now set eval_setting for every binary variable corresponding to
			// var
			int cnt = getVarCount(var);
			for (int j = 0; j < cnt; j++) {
				Var bvar = getVar(var, j);

				// Get the index of bvar in _alOrder
				if (getBVarSetting(j, assign_val)) {
					eval_setting.set(_alOrder.indexOf(new Integer(bvar._nID)),
							TRUE);
				}
			}
		}

		return eval_setting;
	}

	// ///////////////////////////////////////////////////////////////////////////
	// DD Cache Maintenance
	// ///////////////////////////////////////////////////////////////////////////

	/**
	 * Clear nodes on save list
	 **/
	public void clearSaveNodes() {
		_alSaveNodes.clear();
	}

	/**
	 * Remove node on save list by index
	 **/
	public void removeSaveNode(int index) {
		_alSaveNodes.remove(index);
	}

	/**
	 * Add node to save list, return index
	 **/
	public int addSaveNode(Object dd) {
		if (dd == null) {
			System.out.println("Cannot save null DD");
			Object o = null;
			o.toString();
		}
		_alSaveNodes.add(dd);
		return (_alSaveNodes.size() - 1);
	}

	/**
	 * Flush DD caches and free up memory... optional arguments for list of
	 * intermediate factors to keep (used during VE).
	 **/
	public void flushCaches() {
		flushCaches(null, null);
	}

	public void flushCaches(ArrayList factor_list_1) {
		flushCaches(factor_list_1, null);
	}
	
	public void flushCaches(ArrayList factor_list_1, ArrayList factor_list_2) {
		if (!ALWAYS_FLUSH
				&& ((double) RUNTIME.freeMemory() / (double) RUNTIME
						.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			return; // Still enough free mem to exceed minimum requirements
		}
		_context.clearSpecialNodes();
		if (factor_list_1 != null && factor_list_2 != null) {
			Iterator i = factor_list_1.iterator();
			while (i.hasNext()) {
				Factor f = (Factor) i.next();
				_context.addSpecialNode(f._dd);
			}
			i = factor_list_2.iterator();
			while (i.hasNext()) {
				Factor f = (Factor) i.next();
				_context.addSpecialNode(f._dd);
			}
		}
		Iterator j = _alSaveNodes.iterator();
		while (j.hasNext()) {
			_context.addSpecialNode(j.next());
		}
		_context.flushCaches(false);
	}

	// ///////////////////////////////////////////////////////////////////////////
	// Generic BN Inference Methods
	// ///////////////////////////////////////////////////////////////////////////

	/**
	 * Performs translation from internal to external, use do_calc=false to
	 * determine binary tree width of query.
	 **/
	public Object queryOrig(Set query_vars, Map assign_vars) {
		return queryOrig(query_vars, assign_vars, true);
	}

	public Object queryOrig(Set query_vars, Map assign_vars, boolean do_calc) {

		// Build mapping from query/assign vars to binary version
		ArrayList factors = new ArrayList();
		HashMap operations = new HashMap();
		HashSet pruned_assign_vars = new HashSet();

		// Prune the assign var set based on d-separation
		Iterator i = assign_vars.entrySet().iterator();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			String avar = (String) me.getKey();

			// Check dsep of this evidence var against all query vars
			if (false && isDSeparated(avar, new HashSet(query_vars),
					assign_vars.keySet())) {
				System.out.println(avar + " d-sep from " + query_vars
						+ ", discarding " + avar + "...");
				continue;
			}
			pruned_assign_vars.add(avar);
		}

		// Build the appropriate factors
		HashSet rel_vars = new HashSet();
		MarkUpwardAll(rel_vars, query_vars);
		MarkUpwardAll(rel_vars, pruned_assign_vars);
		i = rel_vars.iterator();
		while (i.hasNext()) {
			String rvar = (String) i.next();
			CPT cpt = (CPT) _hmVar2CPT.get(rvar);
			if (cpt == null) {
				System.out.println("CPT for " + rvar + ": " + cpt
						+ " NOT FOUND... discarding");
				continue;
			}

			ArrayList allvars = new ArrayList();
			allvars.add(cpt._sHead);
			allvars.addAll(cpt._alParents);
			factors.add(new Factor(cpt._dd, allvars));
		}

		// Set up query vars
		i = query_vars.iterator();
		while (i.hasNext()) {

			// Get assignment and add all bvars to list
			String qvar = (String) i.next();
			int cnt = getVarCount(qvar);
			for (int j = 0; j < cnt; j++) {
				Var bvar = getVar(qvar, j);
				operations.put(bvar, QUERY);
			}
		}

		// Set up restriction operations
		i = pruned_assign_vars.iterator();
		while (i.hasNext()) {

			// Get assignment and add all bvars to list
			String avar = (String) i.next();
			String assign = (String) assign_vars.get(avar);
			int assign_val = ((IR.Variable) _ir._network._hmVariables.get(avar))._alValues
					.indexOf(assign);
			if (assign_val < 0) {
				System.out.println("Invalid var assignment: " + avar + "="
						+ assign);
				System.exit(1);
			}
			int cnt = getVarCount(avar);
			for (int j = 0; j < cnt; j++) {
				Var bvar = getVar(avar, j);
				operations.put(bvar,
						getBVarSetting(j, assign_val) ? RESTRICT_TRUE
								: RESTRICT_FALSE);
			}
		}

		// Set up sum out operations
		HashSet sum_vars = new HashSet(rel_vars);
		sum_vars.removeAll(query_vars);
		sum_vars.removeAll(pruned_assign_vars);
		i = sum_vars.iterator();
		while (i.hasNext()) {
			String svar = (String) i.next();

			// Error check
			if (assign_vars.get(svar) != null) {
				System.out.println("Summing out an assigned var... ERROR!");
				Object o = null;
				o.toString();
			}

			int cnt = getVarCount(svar);
			for (int j = 0; j < cnt; j++) {
				Var bvar = getVar(svar, j);
				operations.put(bvar, SUM_OUT);
			}
		}

		// Call the varElim algorithm and return
		return varElimOrig(factors, operations, do_calc);
	}

	/**
	 * Internal inference method - variable references are binary
	 **/
	public Object varElimOrig(ArrayList factors, HashMap operations, boolean do_calc) {

		// TODO: Go through all buckets in order...
		// 1) Multiply all DDs
		// 2) Perform required operations
		// 3) Find next earliest var and insert DD in that bucket
		// along with remaining vars from this set
		//
		// Return DD once last bucket reached

		System.out.println("\nRunning variable elimination");
		int max_var_width = -1;

		// System.out.println("Start factors: " + factors);
		// System.out.println(operations + "\n\n");
		int i, j, k;
		ArrayList query_vars = new ArrayList();
		ArrayList contains_factor = new ArrayList();
		ArrayList not_contains_factor = new ArrayList();
		for (i = 0; i < _alPropOrder.size(); i++) {

			// A little inefficient to use Strings, but probably
			// nothing compared to the DD operations.
			String var = (String) _alPropOrder.get(i);

			// Separate out factors into those containing and not
			// containing var.
			contains_factor.clear();
			not_contains_factor.clear();
			for (j = 0; j < factors.size(); j++) {

				Factor f = (Factor) factors.get(j);
				if (f._hsVars.contains(var)) {
					contains_factor.add(f);
				} else {
					not_contains_factor.add(f);
				}
			}

			if (contains_factor.isEmpty()) {
				continue;
			}

			System.out.print("- Initial factor for " + var + "...");

			// Multiply all factors with var -> dd
			Factor f1 = (Factor) contains_factor.get(0);
			Object dd = f1._dd;
			HashSet new_vars = (HashSet) f1._hsVars.clone();
			for (k = 1; k < contains_factor.size(); k++) {
				Factor f2 = (Factor) contains_factor.get(k);
				new_vars.addAll(f2._hsVars);
				if (do_calc) {
					dd = _context.applyInt(dd, f2._dd, DD.ARITH_PROD); // calc
				}

				// Prune?
				// if (_context.PRUNE_TYPE != DD.NO_REPLACE) {
				// _context.pruneNodes(dd);
				// }

				// Cache maintenance
				int ref = addSaveNode(dd);
				flushCaches(contains_factor, not_contains_factor);
				removeSaveNode(ref);
			}

			System.out.println(_context.countExactNodes(dd) + " nodes, "
					+ _context.getGIDs(dd).size() + " bin vars / "
					+ new_vars.size() + " prop vars, " + MemDisplay());

			// Perform any required operations on this var (i.e. restrict/sum
			// out)
			int cnt = getVarCount(var);
			boolean query = false;
			for (k = 0; k < cnt; k++) {
				Var bvar = getVar(var, k);
				String op = (String) operations.get(bvar);
				System.out.print("- Performing " + bvar + "->" + op);
				if (do_calc) {
					if (op == SUM_OUT) {
						dd = _context.opOut(dd, bvar._nID, DD.ARITH_SUM); // Calc
					} else if (op == RESTRICT_TRUE) {
						dd = _context.restrict(dd, bvar._nID, DD.RESTRICT_HIGH); // Calc
					} else if (op == RESTRICT_FALSE) {
						dd = _context.restrict(dd, bvar._nID, DD.RESTRICT_LOW); // Calc
					} else if (op == QUERY) {
						query = true;
						query_vars.add(bvar);
					} else {
						System.out.println("Invalid op: " + op);
						System.exit(1);
					}
				}

				// Prune?
				// if (op != QUERY && _context.PRUNE_TYPE != DD.NO_REPLACE) {
				// _context.pruneNodes(dd);
				// }

				// Cache maintenance
				int ref = addSaveNode(dd);
				flushCaches(contains_factor, not_contains_factor);
				removeSaveNode(ref);

				// Screen output
				List bin_vars = getVarsFromIDs(_context.getGIDs(dd));
				System.out.println("..." + _context.countExactNodes(dd)
						+ " nodes, " + bin_vars.size() + " bin vars / "
						+ new_vars.size() + " prop vars, " + MemDisplay());
				if (new_vars.size() > max_var_width) {
					max_var_width = new_vars.size();
				}

				// Make sure all bin_vars in dd are among the prop vars that
				// should
				// be in the new factor.
				if (do_calc) {
					Iterator bvi = bin_vars.iterator();
					while (bvi.hasNext()) {
						String bvs = ((Var) bvi.next())._sName;
						Iterator nvi = new_vars.iterator();
						boolean found = false;
						while (!found && nvi.hasNext()) {
							found = (bvs.equals(nvi.next()));
						}
						if (!found) {
							System.out.println("ERROR: " + bvs
									+ " not found among prop vars!");
							System.out.println("Bin vars: " + bin_vars);
							System.out.println("Prop vars: " + new_vars);
							System.exit(1);
						}
					}
				}
			}

			// Make new result
			if (!query) {
				new_vars.remove(var); // Factor should not contain var
			}

			// Add the resulting factor back in
			not_contains_factor.add(new Factor(dd, new_vars));
			factors = (ArrayList) not_contains_factor.clone();
			// System.out.println("Interm factors: " + factors);
		}

		// System.out.println("Result factors: " + factors);

		// Multiply out any remaining factors
		Object dd = ((Factor) factors.get(0))._dd;
		for (j = 1; j < factors.size(); j++) {
			dd = _context.applyInt(dd, ((Factor) factors.get(j))._dd,
					DD.ARITH_PROD);

			// Prune?
			// if (_context.PRUNE_TYPE != DD.NO_REPLACE) {
			// _context.pruneNodes(dd);
			// }

			// Cache maintenance
			int ref = addSaveNode(dd);
			flushCaches();
			removeSaveNode(ref);
		}

		// If not doing calculations, just return tree width of query
		if (!do_calc) {
			return new Integer(max_var_width);
		}

		// Normalize the result (Need P(Q|E), have P(Q^E), compute P(Q^E)/(sum_Q
		// P(Q^E))
		double norm_const = 1d;

		// Determine sum vars
		Object sum_dd = dd;
		Iterator sum_vars = query_vars.iterator();
		while (sum_vars.hasNext()) {
			Var bvar = (Var) sum_vars.next();
			sum_dd = _context.opOut(sum_dd, bvar._nID, DD.ARITH_SUM);

			// Cache maintenance
			int ref1 = addSaveNode(dd);
			int ref2 = addSaveNode(sum_dd);
			flushCaches();
			removeSaveNode(ref2);
			removeSaveNode(ref1);
		}
		if (_context.countExactNodes(sum_dd) != 1) {
			System.out.println("Sum did not yield a constant!\n" + sum_dd);
			System.exit(1);
		}

		// Normalization with ranges [min, max] requires division by the
		// opposite to maintain
		// [min, max] property.
		if (DD.PRUNE_TYPE == DD.REPLACE_RANGE) {
			System.out.println("Range normalization not currently implemented");
			System.exit(1);
		} else {
			double sum_dd_val = _context.getMaxValue(sum_dd);
			// System.out.println("Sum: " + _df.format(sum_dd_val));
			if (sum_dd_val == 0) {
				dd = _context.getConstantNode(0d);
			} else {
				dd = _context.scalarMultiply(dd, 1d / sum_dd_val);
			}
		}

		// Cache maintenance
		int ref = addSaveNode(dd);
		flushCaches();
		removeSaveNode(ref);

		return dd;
	}


	/**
	 * Entry point for a query -- uses D-separation to identify relevant factors for VarElim
	 **/
	public Object query(Set query_vars, Map assign_vars, String inference_type) {

		// Prune the assign var set based on D-separation
		HashSet pruned_assign_vars = new HashSet();
		Iterator i = assign_vars.entrySet().iterator();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			String avar = (String) me.getKey();

			// Check dsep of this evidence var against all query vars
			if (false && isDSeparated(avar, new HashSet(query_vars),
					assign_vars.keySet())) {
				System.out.println(avar + " d-sep from " + query_vars
						+ ", discarding " + avar + "...");
				continue;
			}
			pruned_assign_vars.add(avar);
		}

		// Build the appropriate factors
		ArrayList factors = new ArrayList();
		HashSet rel_vars = new HashSet();
		MarkUpwardAll(rel_vars, query_vars);
		MarkUpwardAll(rel_vars, pruned_assign_vars);
		i = rel_vars.iterator();
		while (i.hasNext()) {
			String rvar = (String) i.next();
			CPT cpt = (CPT) _hmVar2CPT.get(rvar);
			if (cpt == null) {
				System.out.println("CPT for " + rvar + ": " + cpt
						+ " NOT FOUND... discarding");
				continue;
			}

			ArrayList allvars = new ArrayList();
			allvars.add(cpt._sHead);
			allvars.addAll(cpt._alParents);
			factors.add(new Factor(cpt._dd, allvars));
		}

		// Call the varElim algorithm and return
		switch (inference_type.toUpperCase()) {
			case "VAR_ELIM": return varElim(factors, new HashSet(query_vars), assign_vars);
			case "LOOPY_BP": return loopyBP(factors, new HashSet(query_vars), assign_vars);
			case "GIBBS":    return gibbs(factors, new HashSet(query_vars), assign_vars);
			default: System.out.println("Unknown inference method: \"" + inference_type + "\""); return null;
		}
	}

	/**
	 * Internal inference method - variable references are binary
	 * 
	 * @param factors list of type Factor (see inner class definition below)
	 * @param query_vars (the variables being queried -- should not be eliminated)
	 * @param assign_vars (a map of var->assignment indicating the values that all evidence variables take) 
	 * @return for Factor f representing the probabilities over the query_vars, return f._dd
	 **/
	public Object varElim(List factors, Set query_vars, Map assign_vars) {

		System.out.println("\nRunning variable elimination:\n\nVariable order: " + _alPropOrder + "\n\nFactors: " + factors);
		
		// TODO: Fill in this method for Assignment 1, Q4.
		//
		// Note that you can print out most classes to see what is in them (toString() should be defined). 
		// For testing, see README.BAYES_NET in directory src/prob and run PSHell with example scripts.
		// Use the variable order as provided by _alPropOrder (ArrayList of String var names)
		//
		// Use the following methods that do exactly what their names suggest:
		// - Factor multiplyFactors(List factors)
		// - Factor marginalizeFactor(Factor f, String mvar)
		// - Factor restrictFactor(Factor f, String avar, String assign)
		// - Factor normalizeFactor(Factor f)
		
		int max_factor_vars = -1;

		// System.out.println("Start factors: " + factors);
		// System.out.println(operations + "\n\n");
		int i, j, k;
		ArrayList contains_var = new ArrayList();
		ArrayList not_contains_var = new ArrayList();
		for (i = 0; i < _alPropOrder.size(); i++) {

			// A little inefficient to use Strings, but probably
			// nothing compared to the DD operations.
			String var = (String) _alPropOrder.get(i);
			if (query_vars.contains(var))
				continue;

			// Separate out factors into those containing and not
			// containing var.
			contains_var.clear();
			not_contains_var.clear();
			for (j = 0; j < factors.size(); j++) {
				Factor f = (Factor) factors.get(j);
				if (f._hsVars.contains(var))
					contains_var.add(f);
				else
					not_contains_var.add(f);
			}

			if (contains_var.isEmpty())
				continue;

			// Multiply all factors with var -> dd
			Factor f = multiplyFactors(contains_var);
			max_factor_vars = Math.max(max_factor_vars, f._hsVars.size());
			System.out.println("Joint factor: " + f);
			System.out.println(" -> eliminating " + var);

			// Perform any required operations on this var (i.e. restrict or sum out)
			String assign = (String)assign_vars.get(var);
			if (assign != null) 
				f = restrictFactor(f, var, assign);
			else
				f = marginalizeFactor(f, var);

			// Add the resulting factor back in
			not_contains_var.add(f);
			factors.clear();
			factors.addAll(not_contains_var);
			
			flushCaches(contains_var, not_contains_var);
			System.out.println("New factor: " + f);
		}

		System.out.println("Result factors:  " + factors);
		System.out.println("Max factor vars: " + max_factor_vars);

		// Multiply out any remaining factors
		Factor norm_result = normalizeFactor( multiplyFactors(factors) );

		// Flush caches of all computations above
		int ref = addSaveNode(norm_result._dd);
		flushCaches();
		removeSaveNode(ref);

		return norm_result._dd;
	}

	/**
	 * Internal inference method - variable references are binary -- same method description as varElim
	 * 
	 * @param factors list of type Factor (see inner class definition below)
	 * @param query_vars (the variables being queried -- should not be eliminated)
	 * @param assign_vars (a map of var->assignment indicating the values that all evidence variables take) 
	 * @return for Factor f representing the probabilities over the query_vars, return f._dd
	 **/
	public Object loopyBP(ArrayList factors, HashSet query_vars, Map assign_vars) {

		// We can only return singleton marginals with Loopy BP so make sure query is legal
		if (query_vars.size() != 1) {
			System.err.println("ERROR: Loopy BP can only answer marginal queries, cannot be applied to P(" + query_vars + " | ...)");
			return null; 
		}
		String query_var = (String)query_vars.iterator().next(); // Get the single query variable
		
		// Just define constants locally for now
		double DAMPING   = 0.9; 
		double TOLERANCE = 0.0001; 
		int MAX_ITER = 100;
		
		// Going to mix in some strongly typed generics (saves a lot of casting)
		HashMap<String,ArrayList<Factor>> var2factor = new HashMap<String,ArrayList<Factor>>(); // var -> [ list of factors that contain var ]
		HashMap<Pair<String,Factor>,Factor> q_msg = new HashMap<Pair<String,Factor>,Factor>();  // var X factor -> q_var->factor
		HashMap<Pair<Factor,String>,Factor> r_msg = new HashMap<Pair<Factor,String>,Factor>();  // factor X var -> r_factor->var
		
		// Build the Map of vars to their list of *restricted* Factor's and all messages (factor <-> var)
		for (Object fo : factors) {
			Factor f = (Factor)fo;
			
			// Restrict the factor if necessary!
			for (Object vo : f._hsVars) {
				String var = (String)vo;
				String assign = (String)assign_vars.get(var); // Is var in factor f restricted?
				if (assign != null) 
					f = restrictFactor(f, var, assign);
			}
			
			// Build key data structures
			for (Object vo : f._hsVars) {
				String var = (String)vo;
				
				// Augment var2factor
				ArrayList<Factor> flist = var2factor.get(var);
				if (flist == null) {
					flist = new ArrayList<Factor>();
					var2factor.put(var, flist);
				}
				flist.add(f);
				
				// Initialize all messages to uniform (set to 1, then normalize)
				HashSet singleton_var = new HashSet();
				singleton_var.add(var);
				q_msg.put(new Pair<String, Factor>(var, f), normalizeFactor( new Factor(_context.getConstantNode(1d), singleton_var)) );
				r_msg.put(new Pair<Factor, String>(f, var), normalizeFactor( new Factor(_context.getConstantNode(1d), singleton_var)) );
			}
		}
		
		// Repeat Loopy BP until either max iterations or complete convergence (marginals do not change)
		int iter = 1;
		Factor answer = new Factor(_context.getConstantNode(2d), query_vars); // Not a probability so cannot be answer --> prevent erroneous convergence on first iter
		Factor old_answer = null;
		double max_diff = -1d;
		do {
			old_answer = answer;
			answer = new Factor(_context.getConstantNode(1d), query_vars);
			ArrayList<Factor> target_r_msgs = new ArrayList<Factor>();
			
			// From factor m to every variable n, store a message rm->n over variable n
			// - Multiply factor m with product over incoming messages qn'->m from all other variables n' and marginalize over n'
			for (Pair<Factor, String> r_key : r_msg.keySet()) { // r_key._o1 = Factor m, r_key._o2 = String var n
				Factor rfun = r_msg.get(r_key); 
				
				// Key r message update computation
				ArrayList<Factor> qmsgs = collectQMsgsWithTargetFactor(q_msg, r_key._o1, r_key._o2);
				// TODO START
				qmsgs.add(r_key._o1);
				Factor new_rfun = multiplyFactors( qmsgs );
				for (Object vo : new_rfun._hsVars) { // Marginalize over all n' != n
					String mvar = (String)vo;
					if (mvar.equals(r_key._o2))
						continue;
					new_rfun = marginalizeFactor(new_rfun, mvar);
				}
				new_rfun = normalizeFactor(new_rfun);
				// TODO STOP
				
				// Mix in new message with old
				rfun = weightedAvgFactors(new_rfun, rfun, DAMPING /* weight of first arg */);
				r_msg.put(r_key, rfun); // Make sure to store result!
			}
			
			// From variable n to every factor m, store a message qn->m over variable n
			// - For all factors m' that n belongs to (except for m), multiply rm'->n together and normalize 
			for (Pair<String, Factor> q_key : q_msg.keySet()) { // q_key._o1 = String var n, q_key._o2 = Factor m
				Factor qfun = q_msg.get(q_key);
				
				// Key q message update computation
				ArrayList<Factor> rmsgs = collectRMsgsWithTargetVar(r_msg, q_key._o1, q_key._o2);

				// TODO START
				if (rmsgs.isEmpty()) // This is a leaf variable in only one factor which always broadcasts the same message
					continue; // System.out.println("Only 1 factor for " + q_key._o1 + " which is " + q_key._o2);
				Factor new_qfun = normalizeFactor( multiplyFactors( rmsgs ) );
				// TODO STOP

				// Mix in new message with old
				qfun = weightedAvgFactors(new_qfun, qfun, DAMPING /* weight of first arg */);
				q_msg.put(q_key, qfun); // Make sure to store result!
			}
			
			// Multiply all target r messages (r_m->n for all m with n=query_var) and normalize to get answer: P(query_var)
			ArrayList<Factor> rmsgs_to_query_var = collectRMsgsWithTargetVar(r_msg, query_var, null /* nothing to exclude */);
			// TODO START
			answer = normalizeFactor( multiplyFactors( rmsgs_to_query_var ) );
			// TODO STOP
			
			// Diagnostic printout
			max_diff = maxDiff(answer, old_answer); // Find answer function value with maximal difference over the last two iterations
			System.out.println("P(" + query_var + "|" + assign_vars + ") on iter #" + iter + ": [diff:" + _df.format(max_diff) + (max_diff <= TOLERANCE ? " CONVERGED!" : "") +"]\n" + answer);
			
		} while (iter++ < MAX_ITER && max_diff > TOLERANCE); 
		
		return answer._dd;
	}

	// Does what it says!
	public ArrayList<Factor> collectQMsgsWithTargetFactor(HashMap<Pair<String,Factor>,Factor> q_msg, Factor target_m, String exclude_var) {
		
		ArrayList<Factor> ret_list = new ArrayList<Factor>();
		for (Pair<String,Factor> q_key : q_msg.keySet())
			if (q_key._o2 == target_m && !q_key._o1.equals(exclude_var))
				ret_list.add(q_msg.get(q_key));
		
		return ret_list;
	}

	// Does what it says!
	public ArrayList<Factor> collectRMsgsWithTargetVar(HashMap<Pair<Factor,String>,Factor> r_msg, String target_var, Factor exclude_factor) {
		
		ArrayList<Factor> ret_list = new ArrayList<Factor>();
		for (Pair<Factor,String> r_key : r_msg.keySet())
			if (r_key._o2.equals(target_var) && r_key._o1 != exclude_factor)
				ret_list.add(r_msg.get(r_key));
		
		return ret_list;
	}
	
	/**
	 * Internal inference method - variable references are binary -- same method description as varElim
	 * 
	 * @param factors list of type Factor (see inner class definition below)
	 * @param query_vars (the variables being queried -- should not be eliminated)
	 * @param assign_vars (a map of var->assignment indicating the values that all evidence variables take) 
	 * @return for Factor f representing the probabilities over the query_vars, return f._dd
	 **/
	public Object gibbs(ArrayList factors, HashSet hashSet, Map assign_vars) {
		return null;
	}

	/** Find the maximum absolute difference between any two values of f1 and f2 **/
	public double maxDiff(Factor factor1, Factor factor2) {

		if (!factor1._hsVars.equals(factor2._hsVars)) {
			System.out.println("ERROR: mismatched var sets, cannot combined damped factors " + factor1 + "\nAND\n" + factor2);
			System.exit(1);
		}
	
		// Compute difference of two factors
		Factor diff1 = new Factor(_context.applyInt(factor1._dd, factor2._dd, DD.ARITH_MINUS), factor1._hsVars);
		Factor diff2 = new Factor(_context.applyInt(factor2._dd, factor1._dd, DD.ARITH_MINUS), factor1._hsVars);
		
		// Max out all variables to find single max difference
		return Math.max( findMax(diff1), findMax(diff2) );
	}
	 
	/** Finds the maximum function value for the factor **/
	public double findMax(Factor f) {
		
		// Max out all variables to find single max difference
		Object dd = f._dd;
		for (Object var : f._hsVars) {
			String mvar = (String)var;
			int cnt = getVarCount(mvar);
			for (int j = 0; j < cnt; j++) {
				Var bvar = getVar(mvar, j);
				dd = _context.opOut(dd, bvar._nID, DD.ARITH_MAX);
			}
		}

		// Must be down to a constant, evaluate the DD and return it
		return _context.evaluate(dd, new ArrayList());
	}
	
	/** Returns the result of multiplying the list of factors **/
	public Factor weightedAvgFactors(Factor factor1, Factor factor2, double weight_factor1) {
		
		if (!factor1._hsVars.equals(factor2._hsVars)) {
			System.out.println("ERROR: mismatched var sets, cannot combined damped factors " + factor1 + "\nAND\n" + factor2);
			System.exit(1);
		}
		
		if (weight_factor1 < 0d || weight_factor1 > 1d) {
			System.out.println("ERROR: cannot compute weighted average without weight in [0,1]: " + weight_factor1);
			System.exit(1);
		}
		
		Object dd1 = _context.scalarMultiply(factor1._dd, weight_factor1);
		Object dd2 = _context.scalarMultiply(factor2._dd, 1.0 - weight_factor1);
		Object dd_result = _context.applyInt(dd1, dd2, DD.ARITH_SUM);
		
		return new Factor(dd_result, factor1._hsVars);
	}

	/** Returns the result of multiplying the list of factors **/
	public Factor multiplyFactors(List factors) {
		Factor f1 = (Factor) factors.get(0);
		Object dd = f1._dd;
		HashSet new_vars = (HashSet) f1._hsVars.clone();
		for (int k = 1; k < factors.size(); k++) {
			Factor f2 = (Factor) factors.get(k);
			new_vars.addAll(f2._hsVars);
			dd = _context.applyInt(dd, f2._dd, DD.ARITH_PROD); 
			
			// Cache maintenance -- is this safe?
			int ref = addSaveNode(dd);
			flushCaches();
			removeSaveNode(ref);
		}

		return new Factor(dd, new_vars);
	}

	/** Returns the result of marginalizing out mvar from the factor **/
	public Factor marginalizeFactor(Factor f, String mvar) {
		Object dd = f._dd;
		
		int cnt = getVarCount(mvar);
		for (int j = 0; j < cnt; j++) {
			Var bvar = getVar(mvar, j);
			dd = _context.opOut(dd, bvar._nID, DD.ARITH_SUM);
		}
		
		HashSet new_vars = new HashSet(f._hsVars); 
		new_vars.remove(mvar);
		return new Factor(dd, new_vars);
	}

	/** Returns the result of setting avar=assign in the factor **/
	public Factor restrictFactor(Factor f, String avar, String assign) {
		Object dd = f._dd;
		
		// Get assignment to all underlying boolean vars (bvars) for avar=assign and restrict the DD to bvars
		int assign_val = ((IR.Variable) _ir._network._hmVariables.get(avar))._alValues.indexOf(assign);
		if (assign_val < 0) { // Error check
			System.out.println("Invalid var assignment: " + avar + "=" + assign);
			System.exit(1);
		}
		int cnt = getVarCount(avar);
		for (int j = 0; j < cnt; j++) {
			Var bvar = getVar(avar, j);
			dd = _context.restrict(dd, bvar._nID, getBVarSetting(j, assign_val) ? DD.RESTRICT_HIGH : DD.RESTRICT_LOW);
		}
		
		HashSet new_vars = new HashSet(f._hsVars); 
		new_vars.remove(avar);
		return new Factor(dd, new_vars);
	}

	/** Assuming all evidence instantiated, sums over all free variables and normalizes the factor by this sum **/
	public Factor normalizeFactor(Factor f) {
		// Normalize the result (Need P(Q|E), have P(Q^E), compute P(Q^E)/(sum_Q P(Q^E))

		// Determine sum vars
		Object sum_dd = f._dd;
		Iterator sum_vars = f._hsVars.iterator();
		while (sum_vars.hasNext()) {
			
			String var = (String) sum_vars.next();
			
			int cnt = getVarCount(var);
			for (int j = 0; j < cnt; j++) {
				Var bvar = getVar(var, j);
				sum_dd = _context.opOut(sum_dd, bvar._nID, DD.ARITH_SUM);
			}

			// Cache maintenance -- is this safe?
			int ref1 = addSaveNode(f._dd);
			int ref2 = addSaveNode(sum_dd);
			flushCaches();
			removeSaveNode(ref2);
			removeSaveNode(ref1);
		}
		if (_context.countExactNodes(sum_dd) != 1) {
			System.out.println("Sum did not yield a constant!\n" + sum_dd);
			System.exit(1);
		}
		double norm_const = _context.getMaxValue(sum_dd);
		Object norm_dd = _context.scalarMultiply(f._dd, 1d / norm_const);
		Factor new_f = new Factor(norm_dd, f._hsVars);
		
		return new_f;
	}
	
	public class Factor {
		public Object _dd;
		public HashSet _hsVars;

		public Factor(Object dd, Collection vars) {
			_dd = dd;
			_hsVars = new HashSet(vars);
		}

		public String toString() {
			
			StringBuilder s = new StringBuilder("Factor( " + _hsVars + "::" + _context.getGIDs(_dd) + " )\n");
			if (_hsVars.size() <= 5)
				s.append(printProbTable());
			else {
				s.append("<Too many vars to print prob table, just showing variable values>\n");
				s.append(printVarValues());
			}
			return s.toString();
		}

		public String printVarValues() {
			StringBuilder sb = new StringBuilder();
			for (Object var : _hsVars) {
				sb.append(var + " in {");
				ArrayList values = getValues((String)var);
				boolean first = true;
				for (Object val : values) {
					sb.append((first ? " " : ", ") + val);
					first = false;
				}
				sb.append(" }\n");
			}
			return sb.toString();
		}
		
		public String printProbTable() {
			if (DD.PRUNE_TYPE == DD.REPLACE_RANGE)
				return "Range cpt printing not implemented";

			StringBuilder sb = new StringBuilder();
			printProbEntries(new HashMap(), new LinkedList(_hsVars), sb);
			return sb.toString();
		}

		public void printProbEntries(HashMap query_assigned, LinkedList query_left, StringBuilder sb) {

			if (query_left.isEmpty()) {

				// Generate output
				sb.append("- " + _df.format(_context.evaluate(_dd, assign2EvalSetting(query_assigned))) + ": P( ");
				Iterator i = query_assigned.entrySet().iterator();
				while (i.hasNext()) {
					Map.Entry me = (Map.Entry) i.next();
					String var = (String) me.getKey();
					String setting = (String) me.getValue();
					sb.append(var + "=" + setting + " ");
				}
				sb.append(")\n");
				return;

			} else {

				// Get next var and recurse for all values
				String var = (String) query_left.removeFirst();
				ArrayList values = getValues(var);
				Iterator j = values.iterator();
				while (j.hasNext()) {
					String val = (String) j.next();
					query_assigned.put(var, val);

					// Recurse
					printProbEntries(query_assigned, query_left, sb);

					query_assigned.remove(var);
				}

				// Now reset so that parent can recurse on other values
				query_left.addFirst(var);
				return;
			}
		}
		
	}

	// ///////////////////////////////////////////////////////////////////////////
	// Miscellaneous
	// ///////////////////////////////////////////////////////////////////////////

	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("\nBN Definition:\n===============\n");
		sb.append("\nVars:       " + _hmVarMap.values() + "\n");
		sb.append("\nOrder:      " + _alOrder + "\n");
		sb.append("\nVar2Cnt:    " + _hmVar2Count + "\n");
		sb.append("\nStrVar2ID:  " + _hmStrVar2ID + "\n");
		sb.append("\nVar2CPT:    " + _hmVar2CPT + "\n");

		// sb.append("\n\nPARENTS: " +_hmParentMap);
		// sb.append("\n\nCHILDREN: " + _hmChildMap);

		return sb.toString();
	}

	public String printQuickStats() {

		StringBuffer sb = new StringBuffer();
		Iterator i = _hmVar2CPT.values().iterator();
		double accum = 0.0d;
		double min = Double.POSITIVE_INFINITY;
		double max = Double.NEGATIVE_INFINITY;
		int entry_count = 0;
		while (i.hasNext()) {
			CPT cpt = (CPT) i.next();
			double ratio = cpt.getCompressionRatio();
			entry_count += cpt._nEntries;
			accum += ratio * cpt._nEntries;
			min = (min < ratio) ? min : ratio;
			max = (max > ratio) ? max : ratio;
		}
		sb.append("\n  Filename................. " + _sShortFilename);
		sb.append("\n  Variables................ " + _alPropOrder.size()
				+ " / " + _alOrder.size());
		sb.append("\n  Parent links............. " + _nParentLinks);
		sb.append("\n  Total nodes.............. " + _nTotalNodes);
		sb.append("\n  Tree width of order...... " + _nTreeWidth);
		sb.append("\n  CPT type................. "
				+ ((DD_TYPE == DD.TYPE_ADD) ? "ADD"
						: ((DD_TYPE == DD.TYPE_AADD) ? "AADD"
								: ((DD_TYPE == DD.TYPE_TABLE) ? "TABLE"
										: "Unknown"))));
		sb.append("\n  Compression percentage... "
				+ _df.format(100d * accum / (double) entry_count) + "% ["
				+ _df.format(min * 100d) + "%, " + _df.format(max * 100d)
				+ "%]");
		sb.append("\n  Time to load............. "
				+ _df.format(_lLoadTime / 1e3) + " s");
		sb.append("\n  Memory usage............. " + MemDisplay());

		return sb.toString();
	}

	public static void SetDDType(int dd_type) {
		DD_TYPE = dd_type;
	}

	// Print out mem used/mem total
	public static String MemDisplay() {
		long total = RUNTIME.totalMemory();
		long free = RUNTIME.freeMemory();
		return _df.format((total - free) / 1e6d) + " Mb / "
				+ _df.format(total / 1e6d) + " Mb";
	}

	// ///////////////////////////////////////////////////////////////////////////
	// Graph Analysis Algorithms
	// ///////////////////////////////////////////////////////////////////////////

	/**
	 * For now, these algorithms work directly on a BN specific version of the
	 * parent/child connectivity graph. This is because the graph package
	 * current does not efficiently store reverse link pointers which are
	 * crucial for determining D-Sep and node sizes which are crucial for d-sep.
	 **/

	/** Determine d-separation **/
	public boolean isDSeparated(String var, Set query_vars, Set evidence) {

		System.out.println("Need to ensure this works correctly... "
				+ "seems to have produced errors"
				+ "\nAlso, _graph.getLinkSet() may return null!!!");
		System.exit(1);

		// Set evidence2 = new HashSet(evidence);
		// evidence2.remove(var);
		boolean isdsep = true;
		Iterator i = query_vars.iterator();
		while (isdsep && i.hasNext()) {
			String qvar = (String) i.next();
			isdsep = isDSeparated(var, qvar, evidence);
		}
		return isdsep;
	}

	/** D-sep algorithm... similar to Bayes-ball algorithm of Schacter **/
	public boolean isDSeparated(String goal, String start, Set evidence) {

		LinkedList nqueue = new LinkedList();

		/* For each evidence node, mark it's parents with a vmark */
		HashSet vmark = new HashSet();
		MarkUpwardAll(vmark, evidence);

		/* Perform a breadth first search from x to y */
		HashSet activepar = new HashSet();
		HashSet activecld = new HashSet();
		activepar.add(start);
		activecld.add(start);
		nqueue.addLast(start);

		while (!nqueue.isEmpty()) {

			String curnode = (String) nqueue.removeFirst();

			if (curnode.equals(goal)) {
				return false; // Reached goal from start, not d-sep!
			}

			/* Insert all children */
			Iterator i = _graph.getRevLinkSet(curnode).iterator();
			while (i.hasNext()) {
				String cld = (String) i.next();
				if (!activepar.contains(cld)) {
					nqueue.addLast(cld);
					activepar.add(cld);
				}
			}

			/* Insert par if curnode active through cld */
			if (activecld.contains(curnode)) {

				/* Insert all parents */
				i = _graph.getLinkSet(curnode).iterator();
				while (i.hasNext()) {
					String par = (String) i.next();
					if (!activecld.contains(par) && !evidence.contains(par)) {
						nqueue.addLast(par);
						activecld.add(par);
					}
				}
			}

			/* If node or descendant is evidence */
			if (vmark.contains(curnode)) {

				/* Check all parents */
				i = _graph.getLinkSet(curnode).iterator();
				while (i.hasNext()) {
					String par = (String) i.next();
					if (!activecld.contains(par)) {

						/*
						 * par not currently active through cld so see if it
						 * should be due to a vstruct
						 */
						Iterator j = _graph.getLinkSet(curnode).iterator();
						while (j.hasNext()) {
							String par2 = (String) j.next();
							if (!par.equals(par2)
									&& (activecld.contains(par2) || activepar
											.contains(par2))) {

								nqueue.addLast(par);
								activecld.add(par);
								break;
							}
						}
					}
				}
			}
		}

		/*
		 * Went though entire queue and never reached goal from start so must be
		 * d-sep
		 */
		return true;
	}

	public void MarkUpward(Set markset, String start) {
		if (markset.contains(start)) {
			return;
		}

		markset.add(start);
		Set s = _graph.getLinkSet(start);
		if (s == null) {
			return;
		}
		Iterator i = s.iterator();
		while (i.hasNext()) {
			MarkUpward(markset, (String) i.next());
		}
	}

	public void MarkUpwardAll(Set markset, Collection nodes) {
		Iterator i = nodes.iterator();
		while (i.hasNext()) {
			MarkUpward(markset, (String) i.next());
		}
	}

	// ///////////////////////////////////////////////////////////////////////////
	// Local Classes and Associated Construction Methods
	// ///////////////////////////////////////////////////////////////////////////

	/* Non-static so it can access parent members */
	public class Var {

		public String _sName;
		public String _sStrName; // with # appended
		public int _bVar; // from 0..log_2(cnt), which is this?
		public int _nID; // ID of _sName+"_"+_bVar

		public Var(String name, int bvar) {
			this(name, bvar, ID_CNT++);
		}

		public Var(String name, int bvar, int id) {
			_sName = name;
			_sStrName = _sName + "_" + bvar;
			_bVar = bvar;
			_nID = id;
		}

		public int hashCode() {
			return _sName.hashCode() - _bVar;
		}

		public boolean equals(Object o) {
			Var v = (Var) o;
			return (_sName.equalsIgnoreCase(v._sName) && _bVar == v._bVar);
		}

		public String toString() {
			return _sName + "_" + _bVar + ": " + _nID;
		}

	}

	/* Non-static so it can access parent members */
	public class CPT {

		/* The local object for storing probabilities */
		public String _sHead;
		public ArrayList _alParents;
		public int _nEntries;

		public ArrayList _alVarHead;
		public ArrayList _alVarParents;

		public Object _dd;

		public CPT(String var, IR.CPT ircpt) {

			// Set up variables - without count
			_sHead = ircpt._sChild;
			_alParents = (ArrayList) ircpt._alParents.clone();
			_nEntries = ircpt._tmEntries.size();

			// Now set up count versions
			int cnt = ((Integer) _hmVar2Count.get(_sHead)).intValue();
			_alVarHead = new ArrayList();
			for (int j = 0; j < cnt; j++) {
				_alVarHead.add(getVar(_sHead, j));
			}
			_alVarParents = new ArrayList();
			Iterator vpars = _alParents.iterator();
			while (vpars.hasNext()) {
				String vpar = (String) vpars.next();
				cnt = getVarCount(vpar);
				for (int j = 0; j < cnt; j++) {
					_alVarParents.add(getVar(vpar, j));
				}
			}

			// Now build DD
			if (ircpt._sFunProperty.equalsIgnoreCase("max")) {
				_dd = buildDDFromNoisyOr(ircpt);
			} else {
				_dd = buildDDFromEnum(ircpt);

				// Previous method
				// Object o2 = buildDDFromEnum2(ircpt);
				// System.out.println(o2);
				// System.out.println(_dd);
			}

			// Put this node in the save cache and flush the caches
			if (_dd == null) {
				System.out.println("\nCould not build dd from " + ircpt);
				System.exit(1);
			}
			_nTotalNodes += _context.countExactNodes(_dd);
			addSaveNode(_dd);
			flushCaches();

			// Prune?
			// if (_context.PRUNE_TYPE != DD.NO_REPLACE) {
			// _context.pruneNodes(_dd);
			// }

			System.out.println("... CP: "
					+ _df.format(getCompressionRatio() * 100d) + "%");
		}

		// Efficiently builds the DD for a noisy-or/noisy-max by constructing
		// an ordered tree. Note: This method is quite complex!
		public Object buildDDFromNoisyOr(IR.CPT ircpt) {

			System.out.print("- Building DD for noisy-max CPT: "
					+ ircpt._alParents + " -> " + ircpt._sChild + ", "
					+ _nEntries + " entries");

			// Build the list of bin vars
			ArrayList bin_var_list = new ArrayList();

			// Build the list of prop variable names
			ArrayList prop_var_list = new ArrayList();
			prop_var_list.add(_sHead);
			prop_var_list.addAll(_alParents);

			// First just quickly recompute the number of entries
			int tmentries = _nEntries;
			int cld_values = ((IR.Variable) _ir._network._hmVariables
					.get(ircpt._sChild))._alValues.size();
			_nEntries = cld_values;
			Iterator pars = ircpt._alParents.iterator();
			while (pars.hasNext()) {
				_nEntries *= ((IR.Variable) _ir._network._hmVariables.get(pars
						.next()))._alValues.size();
			}

			// For each child value
			// For the leak term and each parent variable assignment
			// Compute a DD
			//
			TreeMap entry_map = modifyForNoisyMax(ircpt._tmEntries, cld_values);
			TreeMap temp_map = (TreeMap) entry_map.clone(); // Need to use same
															// comparator!
			Object[] dds = new Object[cld_values]; // dd[i] = P(y <= i | X_1 ...
													// X_n)
			// = PI_{i=1..n} P(y <= i | X_i)
			int cld_val; // i == cld_val
			for (cld_val = 0; cld_val < cld_values; cld_val++) {

				// /////////////////////////////////////////////////////////////////
				// Build DD for Child Value
				// /////////////////////////////////////////////////////////////////

				// Start with the leak term
				ArrayList key = new ArrayList();
				key.add(new Integer(cld_val));
				for (int c = 0; c < ircpt._alParents.size(); c++) {
					key.add(new Integer(0));
				}
				dds[cld_val] = _context.getConstantNode(((Double) entry_map
						.get(key)).doubleValue());

				// Go through all entries for cld_val
				Iterator entries = entry_map.entrySet().iterator();
				while (entries.hasNext()) {
					Map.Entry me = (Map.Entry) entries.next();
					key = (ArrayList) me.getKey();
					double val = ((Double) me.getValue()).doubleValue();
					if (((Integer) key.get(0)).intValue() != cld_val) {
						continue;
					}

					// Get this x term
					int x_index = firstNonZero(key, 1);
					if (x_index < 1) {
						continue;
					}
					int cur_val = ((Integer) key.get(x_index)).intValue();
					String pvar = (String) _alParents.get(x_index - 1);
					int bcnt = getVarCount(pvar);

					// Build the entries - go through all other values of pvar
					// and set to 1d
					temp_map.clear();
					temp_map.put(key, new Double(val));
					int valcnt = ((ArrayList) _hmVar2Values.get(pvar)).size();
					for (int valc = 0; valc < valcnt; valc++) {
						if (valc == cur_val) {
							continue;
						}
						ArrayList key2 = (ArrayList) key.clone();
						key2.set(x_index, new Integer(valc));
						temp_map.put(key2, new Double(1d));
					}

					// Build the bin vars
					bin_var_list.clear();
					bin_var_list.addAll(_alVarHead);
					for (int bval = 0; bval < bcnt; bval++) {
						bin_var_list.add(getVar(pvar, bval));
					}
					bin_var_list = reorder(bin_var_list);

					// Now, need to build a tree Y=i X_index -> val (b/c of map
					// mod Y<=i)!
					ArrayList tree = buildFullTree(0, bin_var_list,
							prop_var_list, new boolean[bin_var_list.size()],
							temp_map, 0d);
					dds[cld_val] = _context
							.applyInt(dds[cld_val],
									_context.buildDDFromOrderedTree(tree,
											_hmStrVar2ID), DD.ARITH_PROD);
				}

				// System.out.println("ADD for cld_var: " + cld_val + "\n" +
				// dds[cld_val]);

				if (cld_val > 0) {

					// /////////////////////////////////////////////////////////////////
					// Build DD for Child Value - 1 and Subtract
					// /////////////////////////////////////////////////////////////////

					// Start with the leak term
					key = new ArrayList();
					key.add(new Integer(cld_val - 1));
					for (int c = 0; c < ircpt._alParents.size(); c++) {
						key.add(new Integer(0));
					}
					Object temp_dd = _context
							.getConstantNode(((Double) entry_map.get(key))
									.doubleValue());

					// Go through all entries for cld_val
					entries = entry_map.entrySet().iterator();
					while (entries.hasNext()) {
						Map.Entry me = (Map.Entry) entries.next();
						key = (ArrayList) me.getKey();
						double val = ((Double) me.getValue()).doubleValue();
						if (((Integer) key.get(0)).intValue() != (cld_val - 1)) {
							continue;
						}

						// Get this x term
						int x_index = firstNonZero(key, 1);
						if (x_index < 1) {
							continue;
						}
						key = (ArrayList) key.clone();
						key.set(0, new Integer(cld_val));
						int cur_val = ((Integer) key.get(x_index)).intValue();
						String pvar = (String) _alParents.get(x_index - 1);
						int bcnt = getVarCount(pvar);

						// Build the entries - go through all other values of
						// pvar and set to 1d
						temp_map.clear();
						temp_map.put(key, new Double(val));
						int valcnt = ((ArrayList) _hmVar2Values.get(pvar))
								.size();
						for (int valc = 0; valc < valcnt; valc++) {
							if (valc == cur_val) {
								continue;
							}
							ArrayList key2 = (ArrayList) key.clone();
							key2.set(x_index, new Integer(valc));
							temp_map.put(key2, new Double(1d));
						}

						// Build the bin vars
						bin_var_list.clear();
						bin_var_list.addAll(_alVarHead);
						for (int bval = 0; bval < bcnt; bval++) {
							bin_var_list.add(getVar(pvar, bval));
						}
						bin_var_list = reorder(bin_var_list);

						// Now, need to build a tree Y=i X_index -> val (b/c of
						// map mod Y<=i)!
						ArrayList tree = buildFullTree(0, bin_var_list,
								prop_var_list,
								new boolean[bin_var_list.size()], temp_map, 0d);
						temp_dd = _context.applyInt(temp_dd, _context
								.buildDDFromOrderedTree(tree, _hmStrVar2ID),
								DD.ARITH_PROD);
					}

					// System.out.println("\nADD for cld_var-1: " + (cld_val-1)
					// + "\n" + temp_dd);

					// Now, subtract cld_val-1 off of cld_val
					dds[cld_val] = _context.applyInt(dds[cld_val], temp_dd,
							DD.ARITH_MINUS);

					// System.out.println("\nDifference: " + dds[cld_val]);
				}
			}

			// Now add all together and set dd
			Object ret_dd = dds[0];
			for (cld_val = 1; cld_val < cld_values; cld_val++) {
				ret_dd = _context.applyInt(ret_dd, dds[cld_val], DD.ARITH_SUM);
			}

			// System.out.println("\n\nFinal DD: " + ret_dd);
			// System.out.println(entry_map);
			// System.out.println("--> " + _sHead + ": " + _alParents);
			// System.out.println("--> " + _alVarHead + ": " + _alVarParents);
			// System.out.println(ircpt._tmEntries + "\n");
			// System.exit(1);

			return ret_dd;
		}

		public TreeMap modifyForNoisyMax(TreeMap entries, int cld_values) {

			TreeMap new_entries = (TreeMap) entries.clone();
			new_entries.clear();

			// Process entries for each cld_val
			for (int cld_val = 0; cld_val < cld_values; cld_val++) {

				Iterator entry_it = entries.entrySet().iterator();
				while (entry_it.hasNext()) {
					Map.Entry me = (Map.Entry) entry_it.next();
					ArrayList key = (ArrayList) me.getKey();
					double val = ((Double) me.getValue()).doubleValue();
					if (cld_val == 0) {
						new_entries.put(key, new Double(val));
					} else {

						// cld_val >= 1 so find me for cld_val and
						// sum all vals less than this
						if (((Integer) key.get(0)).intValue() != cld_val) {
							continue;
						}

						// key and val are for cld_val
						ArrayList al_cld_2 = (ArrayList) key.clone();
						for (int cld_val_2 = cld_val - 1; cld_val_2 >= 0; cld_val_2--) {
							al_cld_2.set(0, new Integer(cld_val_2));
							val += ((Double) entries.get(al_cld_2))
									.doubleValue();
						}

						new_entries.put(key, new Double(val));
					}
				}
			}

			return new_entries;
		}

		public int firstNonZero(ArrayList al, int start) {
			for (int c = start; c < al.size(); c++) {
				if (((Integer) al.get(c)).intValue() != 0) {
					return c;
				}
			}
			return -1;
		}

		// This method enumerates all possible trees, attempts to get the
		// entry for each branch
		public Object buildDDFromEnum(IR.CPT ircpt) {

			System.out.print("- Building tree for CPT: " + ircpt._alParents
					+ " -> " + ircpt._sChild + ", " + _nEntries + " entries");

			// Build the list of Vars
			ArrayList bin_var_list = new ArrayList();
			bin_var_list.addAll(_alVarHead);
			bin_var_list.addAll(_alVarParents);
			bin_var_list = reorder(bin_var_list);

			// Build the list of variable names
			ArrayList prop_var_list = new ArrayList();
			prop_var_list.add(_sHead);
			prop_var_list.addAll(_alParents);

			// Build the DD
			CALLS = 0;
			ArrayList tree = buildFullTree(0, bin_var_list, prop_var_list,
					new boolean[bin_var_list.size()], ircpt._tmEntries, 0d);
			// System.out.println("\n\nBuilt tree: " + tree);
			Object dd = _context.buildDDFromOrderedTree(tree, _hmStrVar2ID);
			// System.out.println("\n\nBuilt DD: " + dd);
			return dd;
		}

		// Make bin_var_list order consistent with _alOrder
		public ArrayList reorder(ArrayList bin_var_list) {
			ArrayList ret = new ArrayList();
			Iterator i = _alOrder.iterator();
			while (i.hasNext()) {
				int id = ((Integer) i.next()).intValue();
				Iterator j = bin_var_list.iterator();
				while (j.hasNext()) {
					Var v = (Var) j.next();
					if (v._nID == id) {
						ret.add(v);
						break;
					}
				}
			}
			return ret;
		}

		public ArrayList buildFullTree(int index, ArrayList bin_var_list,
				ArrayList prop_var_list, boolean[] assignments,
				TreeMap entries, double def) {

			// Any vars left?
			ArrayList ret = new ArrayList();
			if (bin_var_list.size() == index) {

				// Print out progress
				CALLS++;
				if (CALLS % 5000 == 0) {
					System.out.print("\n- " + CALLS + "/" + _nEntries + ", "
							+ MemDisplay());
				}

				ret.add(new BigDecimal(""
						+ getValue(bin_var_list, prop_var_list, assignments,
								entries, def)));
				return ret;
			}

			// Branch on next vars
			ret.add(((Var) bin_var_list.get(index))._sStrName);
			assignments[index] = true;
			ret.add(buildFullTree(index + 1, bin_var_list, prop_var_list,
					assignments, entries, def));
			assignments[index] = false;
			ret.add(buildFullTree(index + 1, bin_var_list, prop_var_list,
					assignments, entries, def));

			// Return the tree
			return ret;
		}

		/**
		 * Takes a list of bin vars (best if conforming to alOrder), and a list
		 * of prop vars (cld and parents in correct order for table), and
		 * assignments to bin vars (same order), and entries mapping prop_var
		 * assignments to values --> returns value (if it exists, otherwise 0)
		 **/
		public double getValue(ArrayList bin_var_list, ArrayList prop_var_list,
				boolean[] assignments, TreeMap entries, double def) {

			// Initialize an assignments list
			ArrayList prop_assign = new ArrayList();
			int i;
			for (i = 0; i < prop_var_list.size(); i++) {
				prop_assign.add(new Integer(0));
			}

			// Now, go through each bin_var, and update prop_assign
			for (i = 0; i < assignments.length; i++) {
				Var bvar = (Var) bin_var_list.get(i);
				boolean assign = assignments[i];
				if (!assign) {
					continue;
				}
				int val = (1 << bvar._bVar);
				int index = prop_var_list.indexOf(bvar._sName);
				int old_val = ((Integer) prop_assign.get(index)).intValue();
				prop_assign.set(index, new Integer(old_val + val));
			}

			// Now retrieve the entry
			Double val = (Double) entries.get(prop_assign);
			if (val == null) {
				// for (int j = 0; j < bin_var_list.size(); j++) {
				// System.out.print(bin_var_list.get(j) + ":" + assignments[j] +
				// " ");
				// }
				// System.out.println(" -> [EMPTY]");
				return def;
			} else {
				// for (int j = 0; j < bin_var_list.size(); j++) {
				// System.out.print(bin_var_list.get(j) + ":" + assignments[j] +
				// " ");
				// }
				// System.out.println(" -> " + val);
				return val.doubleValue();
			}
		}

		// Builds enum based on unordered tree... slower.
		public Object buildDDFromEnum2(IR.CPT ircpt) {

			System.out.println("Building tree for CPT: " + ircpt._alParents
					+ " -> " + ircpt._sChild + "...");

			// Build the list of Vars
			ArrayList bin_var_list = new ArrayList();
			bin_var_list.addAll(_alVarHead);
			bin_var_list.addAll(_alVarParents);

			// Build the list of variable names
			ArrayList prop_var_list = new ArrayList();
			prop_var_list.add(_sHead);
			prop_var_list.addAll(_alParents);

			// Build the initial FBR
			Object probs = _context.getConstantNode(0d);

			// Add each prob entry to it
			Iterator i = ircpt._tmEntries.entrySet().iterator();
			int ecount = 0;
			while (i.hasNext()) {
				ecount++;
				Map.Entry me = (Map.Entry) i.next();
				ArrayList assignments = (ArrayList) me.getKey();
				double val = ((Double) me.getValue()).doubleValue();

				// Build the tree for this entry and add to probs
				if (prop_var_list.size() != assignments.size()) {
					System.out.println("Var/assignment size mismatch: "
							+ prop_var_list.size() + "," + assignments.size());
					System.exit(1);
				}
				DD.ResetTimer();
				ArrayList tree = buildTree(0, bin_var_list, prop_var_list,
						assignments, val);
				Object prob = _context.buildDDFromUnorderedTree(tree,
						_hmStrVar2ID);
				probs = _context.applyInt(probs, prob, DD.ARITH_SUM);
				// System.out.println("- Entry " + ecount + "/" + _nEntries +
				// ": " +
				// _context.countExactNodes(probs) + " nodes, " +
				// MemDisplay() + " bytes, " + GetElapsedTime() + " ms");

				// Clear out the computations
				int ref = addSaveNode(probs);
				flushCaches();
				removeSaveNode(ref);
			}

			return probs;
		}

		// This tree may be unordered
		public ArrayList buildTree(int index, ArrayList bin_var_list,
				ArrayList prop_var_list, ArrayList assignments, double val) {

			// Any vars left?
			ArrayList ret = new ArrayList();
			if (bin_var_list.size() == index) {
				ret.add(new BigDecimal("" + val));
				return ret;
			}

			// Get the the remaining assignment
			ArrayList tree = buildTree(index + 1, bin_var_list, prop_var_list,
					assignments, val);

			// Now iterate through current assignments
			ArrayList zero = new ArrayList();
			zero.add(new BigDecimal("" + 0d));
			Var var = (Var) bin_var_list.get(index);
			boolean setting = getBVarSetting(var, prop_var_list, assignments);
			ret.add(var._sStrName);
			if (setting) {
				ret.add(tree);
				ret.add(zero);
			} else {
				ret.add(zero);
				ret.add(tree);
			}

			// Return the tree
			return ret;
		}

		// Print out the CPT
		public String toString() {
			StringBuffer sb = new StringBuffer();
			// sb.append("Child Str: " + _sHead + "   Parents: " + _alParents +
			// "\n");
			sb.append("\n- Child Var:     " + _alVarHead);
			sb.append("\n- Parents:       " + _alVarParents);
			sb.append("\n- Nodes/Entries: [ " + _context.countExactNodes(_dd)
					+ " / " + _nEntries + " ]");
			sb.append("\n- Comp percent:  "
					+ _df.format(getCompressionRatio() * 100d) + "%");
			sb.append("\n\n");
			// sb.append("DD: " + _dd + "\n");
			return sb.toString();
		}

		// Compute the compression ratio for this CPT (#nodes/#entries)
		public double getCompressionRatio() {
			return _context.countExactNodes(_dd) / (double) _nEntries;
		}
	}
}
