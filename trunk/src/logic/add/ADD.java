//////////////////////////////////////////////////////////////////////
//
// Algebraic Decision Diagram Package
//
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
// TODO:
// -----
// - Also - an information directed reordering routine!
//
// - Outer shell for managing FOL/FOADD - think about this
//   1) Need formula representation, NNF, quantifier push-down
//      routines, simplify closed formula (TP - method in FOADD doc)
//   2) Need package to turn formulae into FOADDs...
//       a) Processes formula into normal form
//       b) Simplifies closed formula (TP)
//       c) Assigns each formula id by TP (incl ~form) or makes new id
//       d) Returns ADD structure where var ids are understood
//          to correspond to the FOLKbs form->id mapping
//       e) Need to work out regression details (existential 
//          introduction and impact)
//
// - (LATER) Other size optimize routines - Rudell?
//
// - Note: SNode code removed for now.
//
//////////////////////////////////////////////////////////////////////

package logic.add;

import graph.Graph;
import util.MapList;

import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

/**
 * General class for implementation of ADD data structure
 **/
public class ADD extends DD {

	// Internal statistics
	public static long APPLY_CALLS = 0;
	public static int OR_PRUNE_CNT = 0;
	public static int AND_PRUNE_CNT = 0;
	public static int PROD_PRUNE_CNT = 0;
	public static int MIN_PRUNE_CNT = 0;
	public static int MAX_PRUNE_CNT = 0;
	public static int PRECISION_PRUNES = 0;
	public static int PRUNE_CACHE_HITS = 0;

	// Local data for ADD
	public int _nLocalIDCnt; // counter for local ids
	public int _nRoot; // local id of root node
	public HashMap _hmADDNodes; // array index gives localID for node
	public HashMap _hmPairs; // <ADD-v1-id, ADD-v2-id> -> ADDNode (for ADD-3)
	// (Apply cache)
	public HashMap _hmReduceMap; // <id-of-node-to-reduce> -> ADDNode (reduced)
	public HashMap _hmPruneMap; // map of node prunes
	public HashMap _hmINodeCache; // <global-id, low, high> -> ADDINode
	public HashMap _hmDNodeCache; // <min-val, max-val> -> ADDDNode
	public int[] _aBNodeCache; // <bin-val> -> ADDBNode

	public HashMap _hmNewADDNodes = null;
	public HashMap _hmNewINodeCache = null;
	public HashMap _hmNewDNodeCache = null;

	public ADDRNode _tmpADDRNode = new ADDRNode(INVALID);

	// /////////////////////////////////////////////////////////////////
	// Basic and copy constructors
	// /////////////////////////////////////////////////////////////////

	public ADD(ArrayList order) {

		_nLocalIDCnt = 0;
		_nRoot = 0;
		_alOrder = (ArrayList) order.clone();

		_hmADDNodes = new HashMap();
		_hmGVarToLevel = new HashMap();
		_hmPairs = new HashMap();
		_hmReduceMap = new HashMap();
		_hmPruneMap = new HashMap();
		_hmINodeCache = new HashMap();
		_hmDNodeCache = new HashMap();
		_aBNodeCache = new int[2];
		_aBNodeCache[0] = _aBNodeCache[1] = INVALID;
		// _nWhich = 0;

		// Build map from global var to order level
		_hmGVarToLevel.clear();
		for (int i = 0; i < _alOrder.size(); i++) {
			_hmGVarToLevel.put((Integer) _alOrder.get(i), new Integer(i));
		}
	}

	public ADD(ADD src) {

		_nLocalIDCnt = 0;

		_hmADDNodes = new HashMap();
		_hmPairs = new HashMap();
		_hmReduceMap = new HashMap();
		_hmPruneMap = new HashMap();
		_hmINodeCache = new HashMap();
		_hmDNodeCache = new HashMap();
		_aBNodeCache = new int[2];
		_aBNodeCache[0] = _aBNodeCache[1] = INVALID;
		// _nWhich = 0;

		// Takes care of root, order, gvar_map, nodeLevel
		_alOrder = (ArrayList) src._alOrder.clone();
		_hmGVarToLevel = (HashMap) src._hmGVarToLevel.clone();

		// Copy over the node structure and load the caches
		setRoot(reduceRestrict(src._nRoot, src, -1, -1 /* No op! */));
	}

	public Object clone() {
		return new ADD(this);
	}

	// ////////////////////////////////////////////////////////////////
	// Flushing and special node maintenance
	// ////////////////////////////////////////////////////////////////

	// Designate/remove/clear nodes to persist through flushing
	public void addSpecialNode(int n) {
		_hsSpecialNodes.add(new ADDRNode(n));
	}

	public void removeSpecialNode(int n) {
		_hsSpecialNodes.remove(new ADDRNode(n));
	}

	public void clearSpecialNodes() {
		_hsSpecialNodes.clear();
	}

	// Flush caches but save special nodes
	public void flushCaches(boolean print_info) {

		// Print starting info
		if (print_info) {
			System.out.print("[FLUSHING CACHES... ");
			// showCacheSize();
			ResetTimer();
		}

		// Can always clear these
		_hmPairs = new HashMap();
		_hmReduceMap = new HashMap();
		_hmPruneMap = new HashMap();

		// Set up temporary alternates to these HashMaps
		_hmNewADDNodes = new HashMap();
		_hmNewINodeCache = new HashMap();
		_hmNewDNodeCache = new HashMap();

		// Copy over 'special' nodes then set new maps
		Iterator i = _hsSpecialNodes.iterator();
		while (i.hasNext()) {
			cacheNode((ADDRNode) i.next());
		}
		_hmADDNodes = _hmNewADDNodes;
		_hmINodeCache = _hmNewINodeCache;
		_hmDNodeCache = _hmNewDNodeCache;

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

	public void cacheNode(ADDRNode r) {
		if (_hmNewADDNodes.containsKey(r)) {
			return;
		}
		ADDNode n = (ADDNode) _hmADDNodes.get(r);
		_hmNewADDNodes.put(r, n);
		if (n instanceof ADDINode) {
			ADDINode ni = (ADDINode) n;
			_hmNewINodeCache.put(new SINodeIndex(ni._nGlobalID, ni._nLow,
					ni._nHigh), r);
			cacheNode(new ADDRNode(ni._nLow));
			cacheNode(new ADDRNode(ni._nHigh));
		} else if (n instanceof ADDDNode) {
			ADDDNode d = (ADDDNode) n;
			_hmNewDNodeCache.put(new SDNodeIndex(d._dLower, d._dUpper), r);
		}
	}

	// ////////////////////////////////////////////////////////////////
	// Internal data structure maintenance
	// ////////////////////////////////////////////////////////////////

	// Quick cache snapshot
	public void showCacheSize() {
		System.out.println("APPLY CACHE:  " + _hmPairs.size());
		System.out.println("REDUCE CACHE: " + _hmReduceMap.size());
		System.out.println("INODE CACHE:  " + _hmINodeCache.size() + "\n");
	}

	// Total cache snapshot
	public long getCacheSize() {
		return _hmPairs.size() + _hmReduceMap.size() + _hmINodeCache.size();
	}

	// An exact count for the ADD rooted at _nRoot
	public long countExactNodes(int id) {
		HashSet cset = new HashSet();
		countExactNodesInt(cset, id);
		return cset.size();
	}

	public Set getExactNodes(int id) {
		HashSet cset = new HashSet();
		countExactNodesInt(cset, id);
		return cset;
	}

	public void countExactNodesInt(HashSet cset, int id) {
		if (cset.contains(new Integer(id))) {
			return;
		}
		ADDNode n = getNode(id);
		// Uncomment the following to get internal-only count
		// if (n instanceof ADDDNode) {
		// return;
		// }
		cset.add(new Integer(id));
		if (n instanceof ADDINode) {
			countExactNodesInt(cset, ((ADDINode) n)._nLow);
			countExactNodesInt(cset, ((ADDINode) n)._nHigh);
		}
	}

	public Set getGIDs(int id) {
		HashSet cset = new HashSet();
		HashSet gset = new HashSet();
		collectGIDsInt(cset, gset, id);
		return gset;
	}

	public void collectGIDsInt(HashSet cset, HashSet gset, int id) {
		if (cset.contains(new Integer(id))) {
			return;
		}
		cset.add(new Integer(id));
		ADDNode n = getNode(id);
		if (n instanceof ADDINode) {
			gset.add(new Integer(((ADDINode) n)._nGlobalID));
			collectGIDsInt(cset, gset, ((ADDINode) n)._nLow);
			collectGIDsInt(cset, gset, ((ADDINode) n)._nHigh);
		}
	}

	// ////////////////////////////////////////////////////////////////
	// Node maintenance
	// ////////////////////////////////////////////////////////////////

	// The only way to retrieve an actual ADDNode!!!
	public ADDNode getNode(int local_id) {
		if (local_id >= 0 && local_id < _nLocalIDCnt) {
			return (ADDNode) _hmADDNodes.get(new ADDRNode(local_id));
		} else {
			return null;
		}
	}

	// Set the root node and update ref counts
	public void setRoot(int n) {

		_nRoot = n;
	}

	public int createINode(int gid, int low, int high) {

		// System.out.println("Create: <" + gid + "," + low + "," + high +
		// ">  ->  " + _nLocalIDCnt);

		int lid = _nLocalIDCnt++;
		ADDRNode ref = new ADDRNode(lid);
		ADDINode n = new ADDINode(lid, gid, low, high);
		_hmADDNodes.put(ref, n);
		_hmINodeCache.put(new SINodeIndex(gid, low, high), ref);

		return lid;
	}

	public int createBNode(boolean bval) {
		int lid = _nLocalIDCnt++;
		ADDBNode n = new ADDBNode(lid, bval);
		_hmADDNodes.put(new ADDRNode(lid), n);
		if (bval) {
			_aBNodeCache[1] = lid;
		} else {
			_aBNodeCache[0] = lid;
		}

		return lid;
	}

	public int createDNode(double min_val, double max_val) {

		return createDNode(min_val, max_val, null, null);
	}

	public int createDNode(double min_val, double max_val, String lower_label,
			String upper_label) {

		int lid = _nLocalIDCnt++;
		ADDDNode n = new ADDDNode(lid, min_val, max_val, lower_label,
				upper_label);
		_hmADDNodes.put(new ADDRNode(lid), n);
		_hmDNodeCache.put(new SDNodeIndex(min_val, max_val), new ADDRNode(lid));

		return lid;
	}

	// This actually does low==high simplification in place... very
	// important to ensure ref counts ok since double linking screws
	// things up. WARNING: May not return INode if low==high.
	public int getINode(int gid, int low, int high, boolean create) {

		// First check if low == high... in this case, just perform the
		// obvious equivalent reduction (this saves headaches later)
		if (low == high) {
			return low;
		}

		ADDRNode iret = (ADDRNode) _hmINodeCache.get(new SINodeIndex(gid, low,
				high));
		if (iret != null) {
			return iret._lid;
		} else if (create) {
			return createINode(gid, low, high);
		} else {
			return INVALID;
		}
	}

	public int getBNode(boolean bval, boolean create) {
		int n = (bval ? 1 : 0);
		if (_aBNodeCache[n] > INVALID) {
			return _aBNodeCache[n];
		} else if (create) {
			return createBNode(bval);
		} else {
			return INVALID;
		}
	}

	public int getDNode(double min_val, double max_val, boolean create) {
		return getDNode(min_val, max_val, create, null, null);
	}

	public int getDNode(double min_val, double max_val, boolean create,
			String lower_label, String upper_label) {
		ADDRNode iret = (ADDRNode) _hmDNodeCache.get(new SDNodeIndex(min_val,
				max_val));
		if (iret != null) {
			if (lower_label != null || upper_label != null) {
				ADDDNode d = (ADDDNode) getNode(iret._lid);
				d._sLowerLabel = lower_label;
				d._sUpperLabel = upper_label;
			}
			return iret._lid;
		} else if (create) {
			return createDNode(min_val, max_val, lower_label, upper_label);
		} else {
			return INVALID;
		}
	}

	public void putPair(int id1, int id2, int op, int to_id) {
		_hmPairs.put(new SNodePair(id1, id2, op), new ADDRNode(to_id));
	}

	public int getPair(int id1, int id2, int op) {
		ADDRNode iret = (ADDRNode) _hmPairs.get(new SNodePair(id1, id2, op));
		if (iret == null) {
			return INVALID;
		} else {
			return iret._lid;
		}
	}

	// For terminal node labelling - not involved in computation
	public void setAllDNodeLabels(String lower, String upper) {
		Iterator i = ((Set) _hmDNodeCache.entrySet()).iterator();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			ADDRNode id = (ADDRNode) me.getValue();
			ADDDNode d = (ADDDNode) getNode(id._lid);
			d._sLowerLabel = lower;
			d._sUpperLabel = upper;
		}
	}

	// Set the min/max values for node given by id
	public void setMinMax(int id) {

		ADDINode ni = (ADDINode) getNode(id);
		ADDNode l = getNode(ni._nLow);
		ADDNode h = getNode(ni._nHigh);

		double ldmin_lower, ldmin_upper, ldmax_lower, ldmax_upper;
		double hdmin_lower, hdmin_upper, hdmax_lower, hdmax_upper;

		// Determine values for low node
		if (l instanceof ADDINode) {
			ldmin_lower = ((ADDINode) l)._dMinLower;
			ldmin_upper = ((ADDINode) l)._dMinUpper;
			ldmax_lower = ((ADDINode) l)._dMaxLower;
			ldmax_upper = ((ADDINode) l)._dMaxUpper;
		} else if (l instanceof ADDDNode) {
			ldmin_lower = ldmax_lower = ((ADDDNode) l)._dLower;
			ldmin_upper = ldmax_upper = ((ADDDNode) l)._dUpper;
		} else {
			ldmin_lower = ldmin_upper = ldmax_lower = ldmax_upper = Double.NaN;
		}

		// Determine values for high node
		if (h instanceof ADDINode) {
			hdmin_lower = ((ADDINode) h)._dMinLower;
			hdmin_upper = ((ADDINode) h)._dMinUpper;
			hdmax_lower = ((ADDINode) h)._dMaxLower;
			hdmax_upper = ((ADDINode) h)._dMaxUpper;
		} else if (h instanceof ADDDNode) {
			hdmin_lower = hdmax_lower = ((ADDDNode) h)._dLower;
			hdmin_upper = hdmax_upper = ((ADDDNode) h)._dUpper;
		} else {
			hdmin_lower = hdmin_upper = hdmax_lower = hdmax_upper = Double.NaN;
		}

		// Set min/max values for ni (first is fn, second is lower,upper)
		ni._dMinLower = Math.min(ldmin_lower, hdmin_lower);
		ni._dMinUpper = Math.min(ldmin_upper, hdmin_upper);
		ni._dMaxLower = Math.max(ldmax_lower, hdmax_lower);
		ni._dMaxUpper = Math.max(ldmax_upper, hdmax_upper);
	}

	// ///////////////////////////////////////////////////////////////
	// General ADD operations
	// ///////////////////////////////////////////////////////////////

	/***********
	 * Need to rewrite, not currently used!
	 * 
	 * // Convert the ADD to a BDD with True for == val, and false otherwise
	 * public static ADD GetBDDFromADD(ADD orig, double lower, double upper) {
	 * 
	 * ADD ret_add = new ADD(orig);
	 * 
	 * // Get all DNodes and convert to BNodes Iterator i =
	 * ret_add._hmDNodeCache.entrySet().iterator(); while (i.hasNext()) {
	 * Map.Entry e = (Map.Entry)i.next(); SDNodeIndex dni =
	 * (SDNodeIndex)e.getKey(); ADDRNode id = (ADDRNode)e.getValue();
	 * ret_add._hmADDNodes.put(id, new ADDBNode(id.intValue(), dni._dLowerVal ==
	 * lower && dni._dUpperVal == upper )); } ret_add._hmDNodeCache = new
	 * HashMap(); ret_add = new ADD(ret_add);
	 * 
	 * //System.out.println("BDD From ADD: " + lower + "..." + upper // +
	 * "\nBefore: \n" + orig + "\nAfter: \n" + ret_add);
	 * 
	 * return ret_add; }
	 * 
	 * // Get a list of BDDs from an ADD public static ArrayList
	 * GetBDDsFromADD(ADD orig) {
	 * 
	 * ArrayList bdd_list = new ArrayList(); ArrayList val_list = new
	 * ArrayList(); ArrayList label_list = new ArrayList();
	 * 
	 * // Build a TreeSet of the distinct terminal values TreeSet vals = new
	 * TreeSet(new SDNodeIndex.SDNComparator(false)); // => decreasing Iterator
	 * i = orig._hmDNodeCache.entrySet().iterator(); while (i.hasNext()) {
	 * Map.Entry e = (Map.Entry)i.next(); vals.add( e.getKey() ); ADDRNode id =
	 * (ADDRNode)e.getValue(); label_list.add (
	 * ((ADDDNode)orig.getNode(id.intValue()))._sLowerLabel ); // TODO: Both
	 * Labels! }
	 * 
	 * // Now iterate through these nodes, create the BDDs, and add to ret list
	 * i = vals.iterator(); while (i.hasNext()) { SDNodeIndex cur =
	 * (SDNodeIndex)i.next(); val_list.add( cur ); bdd_list.add(
	 * GetBDDFromADD(orig, cur._dLowerVal, cur._dUpperVal) ); }
	 * 
	 * ArrayList ret_list = new ArrayList(); ret_list.add(val_list);
	 * ret_list.add(bdd_list); ret_list.add(label_list);
	 * 
	 * return ret_list; }
	 **************/

	// Get min for a generic node
	public double getMin(int id) {
		ADDNode n = getNode(id);
		if (n instanceof ADDINode) {
			ADDINode in = (ADDINode) n;
			return in._dMinLower;
		} else if (n instanceof ADDDNode) {
			ADDDNode dn = (ADDDNode) n;
			return dn._dLower;
		} else {
			return Double.NEGATIVE_INFINITY;
		}
	}

	// Get max for a generic node
	public double getMax(int id) {
		ADDNode n = getNode(id);
		if (n instanceof ADDINode) {
			ADDINode in = (ADDINode) n;
			return in._dMaxUpper;
		} else if (n instanceof ADDDNode) {
			ADDDNode dn = (ADDDNode) n;
			return dn._dUpper;
		} else {
			return Double.POSITIVE_INFINITY;
		}
	}

	// Assuming the difference has already taken place, this method
	// finds the maximum difference
	// TODO: Make this work with ADDSNode... only used for FOMDP epsilon
	// convergence
	public double getMaxAbsValue() {

		double max_diff = Double.NEGATIVE_INFINITY;

		// Get all DNodes, negate, make a new cache and replace old cache
		HashMap new_dnode_cache = new HashMap();
		Iterator i = _hmDNodeCache.keySet().iterator();
		while (i.hasNext()) {
			SDNodeIndex dni = (SDNodeIndex) i.next();

			double upper = (dni._dUpperVal < 0) ? -dni._dUpperVal
					: dni._dUpperVal;
			double lower = (dni._dLowerVal < 0) ? -dni._dLowerVal
					: dni._dLowerVal;

			if (max_diff < upper) {
				max_diff = upper;
			}

			if (max_diff < lower) {
				max_diff = lower;
			}
		}

		// Return max diff
		return max_diff;
	}

	// Find the minimum value in an ADD (must be on the lower val)
	public double getMaxValue() {
		return getMaxValue(_nRoot);
	}

	// Find the minimum value in an ADD (must be on the lower val)
	public double getMaxValue(int id) {

		ADDNode root = getNode(id);
		if (root instanceof ADDDNode) {
			return ((ADDDNode) root)._dUpper;
		} else {
			return ((ADDINode) root)._dMaxUpper;
		}
	}

	// Find the minimum value in an ADD (must be on the lower val)
	public double getMinValue() {
		return getMinValue(_nRoot);
	}

	// Find the minimum value in an ADD (must be on the lower val)
	public double getMinValue(int id) {

		ADDNode root = getNode(id);
		if (root instanceof ADDDNode) {
			return ((ADDDNode) root)._dLower;
		} else {
			return ((ADDINode) root)._dMinLower;
		}
	}

	// Complements the terminal BNodes in an ADD
	public ADD complementInPlace() {

		// Swap BNode true and false and update BNodeCache
		int prevTrue = _aBNodeCache[1];
		int prevFalse = _aBNodeCache[0];

		if (prevTrue > INVALID) {
			((ADDBNode) getNode(prevTrue))._bVal = false;
		}
		if (prevFalse > INVALID) {
			((ADDBNode) getNode(prevFalse))._bVal = true;
		}

		_aBNodeCache[1] = prevFalse;
		_aBNodeCache[0] = prevTrue;

		return this;
	}

	// Returns a *new* BDD with complemented terminal BNodes
	public ADD complement() {
		return new ADD(this).complementInPlace();
	}

	// Returns a new ADD with scalar multiplication of terminal nodes
	public int scalarMultiply(int n, double val) {
		return scalarMultiply(n, val, val);
	}

	public int scalarMultiply(int n, double val_lower, double val_upper) {
		int d = getDNode(val_lower, val_upper, true);
		return applyInt(n, d, ARITH_PROD);
	}

	public ADD scalarMultiply(double val) {
		return scalarMultiply(val, val);
	}

	public ADD scalarMultiply(double val_lower, double val_upper) {
		ADD a = new ADD(this);
		a.setRoot(scalarMultiply(a._nRoot, val_lower, val_upper));
		return a;
	}

	public int scalarAdd(int id, double val) {
		int d = getDNode(val, val, true);
		return applyInt(id, d, ARITH_SUM);
	}

	public ADD scalarAdd(double val) {
		ADD ret = new ADD(this);
		ret.setRoot(scalarAdd(ret._nRoot, val));
		return ret;
	}

	public ADD negate() {
		ADD a = new ADD(this);
		a.setRoot(negate(a._nRoot));
		return a;
	}

	public int negate(int id) {
		int d = getDNode(0d, 0d, true);
		return applyInt(d, id, ARITH_MINUS);
	}

	public ADD invert() {
		ADD a = new ADD(this);
		a.setRoot(invert(a._nRoot));
		return a;
	}

	public int invert(int id) {
		int d = getDNode(1d, 1d, true);
		return applyInt(d, id, ARITH_DIV);
	}

	// /////////////////////////////////////////////////////////////////////////
	// Approximation Algorithms
	// /////////////////////////////////////////////////////////////////////////

	// Start at root
	public int pruneNodes(int id) {

		if (PRUNE_TYPE == NO_REPLACE || PRUNE_PRECISION <= 0d)
			return id;

		if ((PRUNE_TYPE != REPLACE_AVG && PRUNE_TYPE != REPLACE_MIN && 
				PRUNE_TYPE != REPLACE_MAX)) {
			System.out.println("Illegal ADD replacement type " + PRUNE_TYPE);
			System.exit(1);
		}

		HashSet leaves = new HashSet();
		collectLeaves(id, leaves);
		//System.out.println(leaves);
		HashMap remap = compressLeaves(leaves);
		//System.out.println(remap);
		//System.exit(1);
		return reduceRemapLeaves(id, remap);
	}

	public int reduceRemapLeaves(int id, HashMap remap) {
		_hmPruneMap.clear();
		return reduceRemapLeaves2(id, remap);
	}
	
	public int reduceRemapLeaves2(int id, HashMap remap) {
		// Have we examined this node id already?
		// System.out.println("Reduce(" + id + ")");
		ADDRNode qret = null;
		ReduceCacheKey key = new ReduceCacheKey(this, 0, 0, id);
		if ((qret = (ADDRNode) _hmPruneMap.get(key)) != null) {
			// System.out.println("In cache, returning: " + qret);
			return qret._lid;
		}

		// Proceed with reduction algorithm
		// System.out.println("Not in cache");
		int ret = INVALID;
		boolean recurse = true;
		ADDNode n = getNode(id);

		// Update caches and reduce if needed
		if (n instanceof ADDBNode) {
			ret = getBNode(((ADDBNode) n)._bVal, true);
		} else if (n instanceof ADDDNode) {
			ADDDNode dn = (ADDDNode) n;
			ADDDNode remap_dnode = (ADDDNode) remap.get(dn);
			if (remap_dnode != null)
				ret = remap_dnode._nLocalID;
			else
				ret = getDNode(dn._dLower, dn._dUpper, true, dn._sLowerLabel,
						dn._sUpperLabel);
		} else { // n instanceof ADDINode so recurse and update caches
			ADDINode ni = (ADDINode) n;

			// Get new low and high branches
			int low = reduceRemapLeaves2(ni._nLow, remap);
			int high = reduceRemapLeaves2(ni._nHigh, remap);

			// Don't recursively delete if low==high since low
			// will be reused although it may not be linked yet.
			// And we know that low will *have* to be used.
			if (low == high) {
				recurse = false;
			}

			// Decide which node to return (takes care of 'low==high' case)
			// System.out.println("Get:    <" + ni._nGlobalID + "," + low +
			// "," + high + ">");
			ret = getINode(ni._nGlobalID, low, high, true);
			// System.out.println("Result: <" + ni._nGlobalID + "," + low +
			// "," + high + ">  ->  " + ret);

			// getINode may return a DNode or BNode if low==high
			if (getNode(ret) instanceof ADDINode) {
				setMinMax(ret);
			}
		}

		_hmPruneMap.put(key, new ADDRNode(ret));

		return ret;
	}

	public void collectLeaves(int id, HashSet nodes) {
		ADDNode n = getNode(id);
		if (n instanceof ADDDNode) {
			nodes.add(n);
		} else {
			ADDINode ni = (ADDINode) n;
			collectLeaves(ni._nLow, nodes);
			collectLeaves(ni._nHigh, nodes);
		}
	}

	public HashMap compressLeaves(HashSet leaves) {

		ArrayList collect = new ArrayList();
		MapList remap = new MapList(false, true /*hash*/);
		double MERGE_PRECISION = PRUNE_PRECISION / 2d;

		// Collect all distinct leaves... if approximate match in 
		// 'collect' then make note in map, otherwise add it to 'collect'
		Iterator i = leaves.iterator();
		collect.clear();
		collect.add((ADDDNode) i.next());
		while (i.hasNext()) {
			ADDDNode d1 = (ADDDNode) i.next();
			for (Iterator j = collect.iterator(); d1 != null && j.hasNext();) {
				ADDDNode d2 = (ADDDNode) j.next();
				if (Math.abs(d1._dLower - d2._dLower) <= MERGE_PRECISION) {
					remap.putValue(d2, d1); // common node -> mapped node
					d1 = null;
				}
			}
			if (d1 != null)
				collect.add(d1);
		}

		// Now build HashMap to remap
		i = collect.iterator();
		HashMap ret_map = new HashMap();
		while (i.hasNext()) {
			ADDDNode common = (ADDDNode) i.next();
			ArrayList remapped = remap.getValues(common);
			double replace_val = common._dLower;
			double minmax = common._dLower;
			for (Iterator j = remapped.iterator(); j.hasNext();) {
				ADDDNode d = (ADDDNode) j.next();
				replace_val += d._dLower;
				minmax = (PRUNE_TYPE == REPLACE_MAX) ? Math.max(minmax,
						d._dLower) : Math.min(minmax, d._dLower);
			}
			if (PRUNE_TYPE == REPLACE_AVG)
				replace_val /= (double) (1 + remapped.size());
			else if (PRUNE_TYPE == REPLACE_MAX || PRUNE_TYPE == REPLACE_MIN)
				replace_val = minmax;
			else {
				System.out.println("Illegal ADD prune type: " + PRUNE_TYPE);
				System.exit(1);
			}

			ADDDNode new_dnode = (ADDDNode) this.getNode(this.getDNode(
					replace_val, replace_val, true));
			ret_map.put(common, new_dnode);
			for (Iterator j = remapped.iterator(); j.hasNext();)
				ret_map.put(((ADDDNode) j.next()), new_dnode);
		}

		return ret_map;
	}

	// Prunes all node structure having impact less than prune_precision.
	// Range included because need a measure of the range induced by the
	// error at the node.
	public int pruneNodes(int id, boolean recurse) {

		// Can immediately check for local ID of 0
		ADDNode n = getNode(id);
		if (n instanceof ADDDNode) {
			return id;
		}

		ADDINode ni = (ADDINode) n;
		double range = ni._dMaxUpper - ni._dMinLower;

		// Check for a range below precision
		if (range <= PRUNE_PRECISION) {

			// This entire subtree has impact less than prune_precision
			// Note: Not making use of DNode ranges here!!! A single
			// ADD can only have one leaf value in this framework,
			// not a range.
			switch (PRUNE_TYPE) {
			case NO_REPLACE:
			case REPLACE_LOW:
			case REPLACE_HIGH: {
			}
				break;
			case REPLACE_MIN: {
				return getDNode(ni._dMinLower, ni._dMinLower, true);
			}
			case REPLACE_MAX: {
				return getDNode(ni._dMaxUpper, ni._dMaxUpper, true);
			}
			case REPLACE_AVG: {
				double avg = (ni._dMaxUpper + ni._dMinLower) / 2d;
				return getDNode(avg, avg, true);
			}
			default: {
				// if (PRUNE_TYPE == REPLACE_RANGE) { // _nWhich == 1
				// return getDNode(ni._dMinLower, ni._dMinLower, true);
				// } else if (PRUNE_TYPE == REPLACE_RANGE && _nWhich == 2) {
				// return getDNode(ni._dMaxUpper, ni._dMaxUpper, true);
				// } else {
				// // System.out.println("Illegal replacement type " +
				// PRUNE_TYPE); // + ", " + _nWhich
				// Object o1 = null; o1.toString();
				// }
				System.out.println("Range replace not implemented yet");
				System.exit(1);
			}
			}
		}

		// Check cache
		ADDRNode retc = null;
		int ret;
		_tmpADDRNode.set(id);
		if ((retc = (ADDRNode) _hmPruneMap.get(_tmpADDRNode)) == null) {

			// Get high and low branches for this INode
			int low = ni._nLow;
			int high = ni._nHigh;

			// Recurse
			if (recurse) {
				low = pruneNodes(low, true);
				high = pruneNodes(high, true);
			}

			// Now compute diff at this level
			double max_abs_diff = Double.POSITIVE_INFINITY;
			ADDNode adiff = getNode(applyInt(low, high, ARITH_MINUS));
			if (adiff instanceof ADDINode) {
				ADDINode adi = (ADDINode) adiff;
				max_abs_diff = Math.max(Math.abs(adi._dMinLower), Math
						.abs(adi._dMaxUpper));
			} else {
				max_abs_diff = Math.abs(((ADDDNode) adiff)._dLower);
			}

			// ///////////////// DEBUG ////////////////////
			// System.out.println("=================================");
			// System.out.println("Difference: " + max_abs_diff);
			// System.out.println(getNode(low).toString(this, 0));
			// System.out.println("---------------------------------");
			// System.out.println(getNode(high).toString(this, 0));
			// System.out.println("---------------------------------");
			// System.out.println(adiff.toString(this, 0));

			// REMOVE!!!
			// double max_abs_diff2 = Double.POSITIVE_INFINITY;
			// ADDNode adiff2 = getNode(applyInt(high, low, ARITH_MINUS));
			// if (adiff2 instanceof ADDINode) {
			// ADDINode adi = (ADDINode)adiff2;
			// max_abs_diff2 = Math.max(Math.abs(adi._dMinLower),
			// Math.abs(adi._dMaxUpper));
			// } else {
			// max_abs_diff2 = Math.abs(((ADDDNode)adiff2)._dLower);
			// }
			// if (Math.abs(max_abs_diff2 - max_abs_diff) >= 1e-9d) {
			// System.out.println("Difference: " + max_abs_diff + " / " +
			// max_abs_diff2);
			// System.out.println("Assymmetric minus... error!!!");
			// System.exit(1);
			// }
			// System.out.println("=================================");
			// ////////////////////////////////////////////

			// Should we prune?
			if ((PRUNE_PRECISION >= 0d) && (max_abs_diff <= PRUNE_PRECISION)) {

				// ///////////////// DEBUG ////////////////////
				// System.out.println("Pruning type: " + PRUNE_TYPE);
				// System.out.println("Difference: " + max_abs_diff);
				// System.out.println("Pruning: \n" + ni.toString(this,0));
				// System.out.println("---------------------------------");
				// ////////////////////////////////////////////

				switch (PRUNE_TYPE) {
				case NO_REPLACE: {
					ret = getINode(ni._nGlobalID, low, high, true);
				}
					break;
				case REPLACE_LOW: {
					ret = low;
				}
					break;
				case REPLACE_HIGH: {
					ret = high;
				}
					break;
				case REPLACE_MIN: {
					ret = applyInt(low, high, ARITH_MIN);
				}
					break;
				case REPLACE_MAX: {
					ret = applyInt(low, high, ARITH_MAX);
				}
					break;
				case REPLACE_AVG: {
					ret = scalarMultiply(applyInt(low, high, ARITH_SUM), 0.5d);
				}
					break;
				default: {
					// if (PRUNE_TYPE == REPLACE_RANGE) { // && _nWhich == 1
					// ret = new ADDRNode(applyInt(low, high, ARITH_MIN));
					// } else if (PRUNE_TYPE == REPLACE_RANGE && _nWhich == 2) {
					// ret = new ADDRNode(applyInt(low, high, ARITH_MAX));
					// } else {
					// System.out.println("Illegal replacement type " +
					// PRUNE_TYPE); // ", " + _nWhich
					// Object o1 = null; o1.toString();
					// }
					ret = INVALID;
					System.out.println("Range replace not implemented yet");
					System.exit(1);
				}
				}

				PRECISION_PRUNES++;

			} else {

				// Retrieve the inode
				ret = getINode(ni._nGlobalID, low, high, true);

			}

			// getINode may return a DNode or BNode if low==high
			if (getNode(ret) instanceof ADDINode) {
				setMinMax(ret);
			}

			// Cache the node in canonical form
			_hmPruneMap.put(new ADDRNode(id), new ADDRNode(ret));

		} else {
			PRUNE_CACHE_HITS++;
			ret = retc._lid;
		}

		// Return cached value modified by offset
		return ret;
	}

	////////////////////////////////////////////////////////////////////////////
	// Main Computation Algorithms
	////////////////////////////////////////////////////////////////////////////

	// Assume already built with correct order, just needs reduction
	public void reduce() {
		setRoot(reduceRestrict(_nRoot, this, -1, -1));
	}

	public int reduce(int root) {
		return reduceRestrict(root, this, -1, -1);
	}

	// Assume already built with correct order, just needs reduction
	public void restrict(int gid, int op) {
		setRoot(reduceRestrict(_nRoot, this, gid, op));
	}

	public int restrict(int root, int gid, int op) {
		return reduceRestrict(root, this, gid, op);
	}

	// If 'src' is non-null, this will obtain the node structure
	// from the ADD given by src. In this case, the src
	// structure will remain unchanged (used for copying, should
	// only be called if 'this' is empty). TODO: Remove printlns!
	public int reduceRestrict(int id, ADD src, int gid, int op) {
		// Have we examined this node id already?
		// System.out.println("Reduce(" + id + ")");
		ADDRNode qret = null;
		ReduceCacheKey key = new ReduceCacheKey(src, gid, op, id);
		if ((qret = (ADDRNode) _hmReduceMap.get(key)) != null) {
			// System.out.println("In cache, returning: " + qret);
			return qret._lid;
		}

		// Proceed with reduction algorithm
		// System.out.println("Not in cache");
		int ret = INVALID;
		boolean recurse = true;
		ADDNode n = src.getNode(id);

		// Update caches and reduce if needed
		if (n instanceof ADDBNode) {
			ret = getBNode(((ADDBNode) n)._bVal, true);
		} else if (n instanceof ADDDNode) {
			ADDDNode dn = (ADDDNode) n;
			ret = getDNode(dn._dLower, dn._dUpper, true, dn._sLowerLabel,
					dn._sUpperLabel);
		} else { // n instanceof ADDINode so recurse and update caches
			ADDINode ni = (ADDINode) n;

			if (ni._nGlobalID == gid) {

				if (op == RESTRICT_HIGH || op == RESTRICT_LOW) {
					ret = ((op == RESTRICT_LOW) ? reduceRestrict(ni._nLow, src,
							gid, op) : reduceRestrict(ni._nHigh, src, gid, op));
				} else {
					System.out.println("ERROR: op not a RESTRICT!");
					Object o = null;
					o.toString();
					System.exit(1);
				}

			} else {

				// Get new low and high branches
				int low = reduceRestrict(ni._nLow, src, gid, op);
				int high = reduceRestrict(ni._nHigh, src, gid, op);

				// Don't recursively delete if low==high since low
				// will be reused although it may not be linked yet.
				// And we know that low will *have* to be used.
				if (low == high) {
					recurse = false;
				}

				// Decide which node to return (takes care of 'low==high' case)
				// System.out.println("Get:    <" + ni._nGlobalID + "," + low +
				// "," + high + ">");
				ret = getINode(ni._nGlobalID, low, high, true);
				// System.out.println("Result: <" + ni._nGlobalID + "," + low +
				// "," + high + ">  ->  " + ret);

				// getINode may return a DNode or BNode if low==high
				if (getNode(ret) instanceof ADDINode) {
					setMinMax(ret);
				}
			}
		}

		// Cache, update structure, and return. Note: If we came
		// in for a node i and left with j (i != j), then we know
		// every other time we come into i, we will return j so we can
		// completely kill off j. (Only do this if 'src' is 'this' -
		// otherwise we can't compare the node IDs!)
		_hmReduceMap.put(key, new ADDRNode(ret));

		// Note: For both ADD and AADD, reduce() may not completely dec all
		// ref counts, but easier to be conservative for now.

		// if ((id != ret) && (src == this)) {
		// //System.out.println("Alternate reduction of " + id + "(del) to " +
		// ret + "(new)");
		// decRefCount(id, true /* delete! */, recurse /* recursive? */);
		// }
		return ret;
	}

	public int opOut(int gid, int op) {
		return opOut(_nRoot, gid, op);
	}

	public int opOut(int rid, int gid, int op) {

		if (op != ARITH_SUM && op != ARITH_PROD && op != ARITH_MAX
				&& op != ARITH_MIN) {
			System.out.println("ERROR: opOut called without SUM/PROD/MIN/MAX");
			Object o = null;
			o.toString();
		}

		// Get high and low branch restrictions for this var
		int high_br = reduceRestrict(rid, this, gid, RESTRICT_HIGH);
		int low_br = reduceRestrict(rid, this, gid, RESTRICT_LOW);

		// Must be called with src b/c nodes will be internalized
		return applyInt(high_br, low_br, op);
	}

	// Remap gids... gid_map = old_id -> new_id (assuming order consistent)
	public int remapGIDsInt(int lid, HashMap gid_map) {
		ADDNode n = getNode(lid);
		//System.out.println(lid + ": " + n);
		if (n instanceof ADDBNode || n instanceof ADDDNode) {
			return lid;
		} else { // n instanceof ADDINode so recurse and update caches
			ADDINode ni = (ADDINode) n;
			Integer old_id = new Integer(ni._nGlobalID);
			Integer new_id = (Integer) gid_map.get(old_id);
			if (new_id == null) {
				new_id = old_id;
			}
			return getINode(new_id.intValue(), remapGIDsInt(ni._nLow, gid_map),
					remapGIDsInt(ni._nHigh, gid_map), true);
		}
	}

	// Assume a1 and a2 are ordered and reduced, op is boolean or +,*,max
	public static ADD Apply(ADD a1, ADD a2, int op) {
		if (op == RESTRICT_LOW || op == RESTRICT_HIGH) {
			System.out.println("Cannot RESTRICT using Apply(...)");
			System.exit(1);
		}

		// Merge the orderings of the two nodes (assuming no conflicts)
		// and build new empty ADD
		ADD result = null;
		result = new ADD(((ADD) a1)._alOrder);
		// result._nWhich = (a1._nWhich != 0) ? a1._nWhich : a2._nWhich;

		// Now that order is correct, apply ops
		result.setRoot(result.apply(((ADD) a1)._nRoot, ((ADD) a1),
				((ADD) a2)._nRoot, ((ADD) a2), op));

		return result;
	}

	// Nodes can be external to this, will be internalized. Result will be
	// within "this".
	public int apply(int a1, ADD ctxt1, int a2, ADD ctxt2, int op) {
		// Compare.ResetTimer();

		if (ctxt1 != this) {
			a1 = reduceRestrict(a1, ctxt1, -1, -1);
		}

		if (ctxt2 != this) {
			a2 = reduceRestrict(a2, ctxt2, -1, -1);
		}

		// System.out.print(" *" + Compare.GetElapsedTime() + "* ");
		// Compare.ResetTimer();
		return applyInt(a1, a2, op);
	}

	public int applyInt(int a1, int a2, int op) {
		int ret = getPair(a1, a2, op);
		if (ret > INVALID) {
			return ret;
		}

		// Can we create a terminal node here?
		ADDNode n1 = getNode(a1), n2 = getNode(a2);
		int t = computeTermNode(n1, n2, op);
		if (t > INVALID) {
			ret = t;
		} else { // At least one non-terminal so must recurse

			int v1low, v1high, v2low, v2high, gid;

			// Find node with min id (or only internal node)
			if (n1 instanceof ADDINode) {
				if (n2 instanceof ADDINode) {
					if (comesBefore(((ADDINode) n1)._nGlobalID,
							((ADDINode) n2)._nGlobalID)) {
						gid = ((ADDINode) n1)._nGlobalID;
					} else {
						gid = ((ADDINode) n2)._nGlobalID;
					}
				} else {
					gid = ((ADDINode) n1)._nGlobalID;
				}
			} else {
				gid = ((ADDINode) n2)._nGlobalID;
			}

			// Determine next recursion for n1
			if ((n1 instanceof ADDINode) && (((ADDINode) n1)._nGlobalID == gid)) {
				ADDINode n1i = (ADDINode) n1;
				v1low = n1i._nLow;
				v1high = n1i._nHigh;
			} else {
				v1low = a1;
				v1high = a1;
			}

			// Determine next recursion for n2
			if ((n2 instanceof ADDINode) && (((ADDINode) n2)._nGlobalID == gid)) {
				ADDINode n2i = (ADDINode) n2;
				v2low = n2i._nLow;
				v2high = n2i._nHigh;
			} else {
				v2low = a2;
				v2high = a2;
			}

			// Perform in-line reduction and set min/max for subnodes if needed
			int low = applyInt(v1low, v2low, op);
			int high = applyInt(v1high, v2high, op);

			// getINode will take care of 'low==high'
			ret = getINode(gid, low, high, true);

			// getINode may return a DNode or BNode if low==high
			if (getNode(ret) instanceof ADDINode) {
				setMinMax(ret);
			}
		}

		putPair(a1, a2, op, ret);
		return ret;
	}

	// Computes a terminal node value if possible, assume
	// terms of same type (otherwise incompatible!)
	public int computeTermNode(ADDNode a1, ADDNode a2, int op) {
		int ret = INVALID;

		switch (op) {

		case LOG_AND: {
			if (((a1 instanceof ADDBNode) && (((ADDBNode) a1)._bVal == false))
					|| ((a2 instanceof ADDBNode) && (((ADDBNode) a2)._bVal == false))) {
				ret = getBNode(false, true /* create if not found! */);
				// System.out.println("AND PRUNE!!!"); // TODO: Remove!!!
				AND_PRUNE_CNT++;

			} else if ((a1 instanceof ADDBNode) && (a2 instanceof ADDBNode)) {
				boolean res = ((ADDBNode) a1)._bVal && ((ADDBNode) a2)._bVal;
				ret = getBNode(res, true /* create if not found! */);
			}
		}
			break;

		case LOG_OR: {
			if (((a1 instanceof ADDBNode) && (((ADDBNode) a1)._bVal == true))
					|| ((a2 instanceof ADDBNode) && (((ADDBNode) a2)._bVal == true))) {
				ret = getBNode(true, true /* create if not found! */);
				// System.out.println("OR PRUNE!!!"); // TODO: Remove!!!
				OR_PRUNE_CNT++;

			} else if ((a1 instanceof ADDBNode) && (a2 instanceof ADDBNode)) {
				boolean res = ((ADDBNode) a1)._bVal || ((ADDBNode) a2)._bVal;
				ret = getBNode(res, true /* create if not found! */);
			}
		}
			break;

		case ARITH_SUM: {
			if ((a1 instanceof ADDDNode) && (a2 instanceof ADDDNode)) {
				double min = ((ADDDNode) a1)._dLower + ((ADDDNode) a2)._dLower;
				double max = ((ADDDNode) a1)._dUpper + ((ADDDNode) a2)._dUpper;
				ret = getDNode(min, max, true);
			}

		}
			break;

		case ARITH_MINUS: {
			if ((a1 instanceof ADDDNode) && (a2 instanceof ADDDNode)) {
				double min = ((ADDDNode) a1)._dLower - ((ADDDNode) a2)._dLower;
				double max = ((ADDDNode) a1)._dUpper - ((ADDDNode) a2)._dUpper;
				if (min > max) {
					double temp = min;
					min = max;
					max = temp;
				}
				ret = getDNode(min, max, true);
			}

		}
			break;

		case ARITH_DIV: {
			if ((a1 instanceof ADDDNode) && (a2 instanceof ADDDNode)) {
				double min = ((ADDDNode) a1)._dLower / ((ADDDNode) a2)._dLower;
				double max = ((ADDDNode) a1)._dUpper / ((ADDDNode) a2)._dUpper;
				if (min > max) {
					double temp = min;
					min = max;
					max = temp;
				}
				ret = getDNode(min, max, true);
			}

		}
			break;

		case ARITH_PROD: {
			if ((a1 instanceof ADDDNode) && (a2 instanceof ADDDNode)) {
				double min = ((ADDDNode) a1)._dLower * ((ADDDNode) a2)._dLower;
				double max = ((ADDDNode) a1)._dUpper * ((ADDDNode) a2)._dUpper;
				ret = getDNode(min, max, true);
			} else if ((a1 instanceof ADDDNode)
					&& (((ADDDNode) a1)._dLower == (double) 0.0)
					&& (((ADDDNode) a1)._dUpper == (double) 0.0)) {
				// System.out.println("PROD PRUNE!!!"); // TODO: Remove!!!
				PROD_PRUNE_CNT++;
				ret = getDNode((double) 0.0, (double) 0.0, true);
			} else if ((a2 instanceof ADDDNode)
					&& (((ADDDNode) a2)._dLower == (double) 0.0)
					&& (((ADDDNode) a2)._dUpper == (double) 0.0)) {
				// System.out.println("PROD PRUNE!!!"); // TODO: Remove!!!
				PROD_PRUNE_CNT++;
				ret = getDNode((double) 0.0, (double) 0.0, true);
			}
		}
			break;

		case ARITH_MIN: { // Can assume an ADD for arithmetic operations
			if ((a1 instanceof ADDDNode) && (a2 instanceof ADDDNode)) {
				ADDDNode a1d = (ADDDNode) a1;
				ADDDNode a2d = (ADDDNode) a2;
				double lower = Math.min(a1d._dLower, a2d._dLower);
				double upper = Math.min(a1d._dUpper, a2d._dUpper);
				ret = getDNode(lower, upper, true,
						(lower == a1d._dLower) ? a1d._sLowerLabel
								: a2d._sLowerLabel,
						(upper == a1d._dUpper) ? a1d._sUpperLabel
								: a2d._sUpperLabel);
			} else if ((a1 instanceof ADDDNode) && (a2 instanceof ADDINode)
					&& (((ADDDNode) a1)._dLower <= ((ADDINode) a2)._dMinLower)
					&& (((ADDDNode) a1)._dUpper <= ((ADDINode) a2)._dMinUpper)) {
				// If a1.lower < a2.min.lower && a1.upper < a2.min.upper
				// then can set node to a1
				ADDDNode a1d = (ADDDNode) a1;
				ret = getDNode(a1d._dLower, a1d._dUpper, true,
						a1d._sLowerLabel, a1d._sUpperLabel);
				// System.out.println("MIN PRUNE!!!"); // TODO: Remove!!!
				MIN_PRUNE_CNT++;
			} else if ((a2 instanceof ADDDNode)
					&& (((ADDDNode) a2)._dLower <= ((ADDINode) a1)._dMinLower)
					&& (((ADDDNode) a2)._dUpper <= ((ADDINode) a1)._dMinUpper)) {
				// If a2.lower < a1.min.lower && a2.upper < a1.min.upper
				// then can set node to a2
				ADDDNode a2d = (ADDDNode) a2;
				ret = getDNode(a2d._dLower, a2d._dUpper, true,
						a2d._sLowerLabel, a2d._sUpperLabel);
				// System.out.println("MIN PRUNE!!!"); // TODO: Remove!!!
				MIN_PRUNE_CNT++;
			}
		}
			break;

		case ARITH_MAX: { // Can assume an ADD for arithmetic operations
			if ((a1 instanceof ADDDNode) && (a2 instanceof ADDDNode)) {
				ADDDNode a1d = (ADDDNode) a1;
				ADDDNode a2d = (ADDDNode) a2;
				double lower = Math.max(a1d._dLower, a2d._dLower);
				double upper = Math.max(a1d._dUpper, a2d._dUpper);
				ret = getDNode(lower, upper, true,
						(lower == a1d._dLower) ? a1d._sLowerLabel
								: a2d._sLowerLabel,
						(upper == a1d._dUpper) ? a1d._sUpperLabel
								: a2d._sUpperLabel);
			} else if ((a1 instanceof ADDDNode) && (a2 instanceof ADDINode)
					&& (((ADDDNode) a1)._dLower >= ((ADDINode) a2)._dMaxLower)
					&& (((ADDDNode) a1)._dUpper >= ((ADDINode) a2)._dMaxUpper)) {
				// If a1.lower > a2.max.lower && a1.upper > a2.max.upper
				// then can set node to a1
				ADDDNode a1d = (ADDDNode) a1;
				ret = getDNode(a1d._dLower, a1d._dUpper, true,
						a1d._sLowerLabel, a1d._sUpperLabel);
				// System.out.println("MAX PRUNE!!!"); // TODO: Remove!!!
				MAX_PRUNE_CNT++;
			} else if ((a2 instanceof ADDDNode)
					&& (((ADDDNode) a2)._dLower >= ((ADDINode) a1)._dMaxLower)
					&& (((ADDDNode) a2)._dUpper >= ((ADDINode) a1)._dMaxUpper)) {
				// If a2.lower > a1.max.lower && a2.upper > a1.max.upper
				// then can set node to a2
				ADDDNode a2d = (ADDDNode) a2;
				ret = getDNode(a2d._dLower, a2d._dUpper, true,
						a2d._sLowerLabel, a2d._sUpperLabel);
				// System.out.println("MAX PRUNE!!!"); // TODO: Remove!!!
				MAX_PRUNE_CNT++;
			}
		}
			break;
		}

		return ret;
	}

	// Takes an assignment of gvars->{T|F} (Boolean class) and returns
	// the corresponding terminal node.
	public double evaluate(int id, ArrayList assign) {

		Boolean b;
		ADDNode cur = getNode(id);

		while (cur instanceof ADDINode) {
			int level = ((Integer) _hmGVarToLevel.get(new Integer(
					((ADDINode) cur)._nGlobalID))).intValue();

			// If we need a var this is unassigned, return null
			if ((level < assign.size())
					&& ((b = (Boolean) assign.get(level)) != null)) {
				ADDINode ni = (ADDINode) cur;
				cur = (b.booleanValue()) ? getNode(ni._nHigh)
						: getNode(ni._nLow);
			} else {
				return Double.NaN;
			}
		}

		// If get here, cur will be an ADDDNode, ADDBNode
		if (cur instanceof ADDDNode) {
			return ((ADDDNode) cur)._dLower;
		} else if (cur instanceof ADDBNode) {
			return ((ADDBNode) cur)._bVal ? 1.0d : 0.0d;
		} else {
			return Double.NaN;
		}
	}

	// ///////////////////////////////////////////////////////////////
	// Order maintenance
	// ///////////////////////////////////////////////////////////////

	// Probably have more efficient ways to do a lot of these using
	// binary search and hash tables

	// Order check - both must occur in list!
	public boolean comesBefore(int gid1, int gid2) {
		// Get level for gid1 and gid2
		int l1 = ((Integer) _hmGVarToLevel.get(new Integer(gid1))).intValue();
		int l2 = ((Integer) _hmGVarToLevel.get(new Integer(gid2))).intValue();

		// Determine which comes first (i.e. earlier level)
		return (l1 <= l2);
	}

	// //////////////////////////////////////////////////////////////
	// Construction and File I/O Routines
	// //////////////////////////////////////////////////////////////

	/**
	 * Build an ADD from a list (node is a list, high comes first for internal
	 * nodes)
	 **/
	public int buildDDFromUnorderedTree(ArrayList l, Map var2ID) {
		Object o = l.get(0);
		if (o instanceof String && HasOnlyDigits((String) o)) {
			double val = (new BigInteger((String) o)).doubleValue();
			return getDNode(val, val, true);
		} else if (o instanceof BigDecimal) {
			double val = ((BigDecimal) o).doubleValue();
			return getDNode(val, val, true);
		} else {
			String var = (String) o;
			if (((Integer) var2ID.get(var)) == null) System.out.println(var);
			int gid = ((Integer) var2ID.get(var)).intValue();

			// Get the var ADD
			int high_br = getVarNode(gid, 0.0d, 1.0d);
			high_br = applyInt(high_br, buildDDFromUnorderedTree((ArrayList) l
					.get(1), var2ID) /* high */, ARITH_PROD);

			// Get the !var ADD
			int low_br = getVarNode(gid, 1.0d, 0.0d);
			low_br = applyInt(low_br, buildDDFromUnorderedTree((ArrayList) l
					.get(2), var2ID) /* low */, ARITH_PROD);

			return applyInt(low_br, high_br, ARITH_SUM);
		}
	}

	/**
	 * Build an ADD from a list with correct variable order (node is a list,
	 * high comes first for internal nodes)
	 **/
	public int buildDDFromOrderedTree(ArrayList l, Map var2ID) {
		return reduce(buildNode(l, var2ID));
	}

	public int buildNode(ArrayList l, Map var2ID) {

		// System.out.println("Building: " + l);

		Object o = l.get(0);
		if (o instanceof String && HasOnlyDigits((String) o)) {
			double v = (new BigInteger((String) o)).doubleValue();
			return getDNode(v, v, true);
		} else if (o instanceof BigDecimal) {
			double v = ((BigDecimal) o).doubleValue();
			return getDNode(v, v, true);
		} else {
			String var = (String) o;
			int gid = ((Integer) var2ID.get(var)).intValue();

			// Get the var ADD
			int high = buildNode((ArrayList) l.get(1), var2ID);
			int low = buildNode((ArrayList) l.get(2), var2ID);
			return getINode(gid, low, high, true);
		}
	}

	public static boolean HasOnlyDigits(String s) {
		for (int i = 0; i < s.length(); i++) {
			if (!Character.isDigit(s.charAt(i)) && s.charAt(i) != '-') {
				return false;
			}
		}
		return true;
	}

	/** Build a var ADD **/
	public int getVarNode(int gid, double low, double high) {

		int n_low = getDNode(low, low, true);
		int n_high = getDNode(high, high, true);
		return getINode(gid, n_low, n_high, true);
	}

	/** Build a constant ADD */
	public int getConstantNode(double val) {
		return getDNode(val, val, true);
	}

	// Takes an assignment of gvars->{T|F} (Boolean class) and returns
	// the corresponding terminal node.
	// TODO: Update ADDSNodes!
	public void dumpToTree(int n, String var_prefix, PrintWriter ps,
			DecimalFormat df, int level) {

		ADDNode cur = getNode(n);

		if (cur instanceof ADDINode) {
			ADDINode i = (ADDINode) cur;
			ps.print("\n" + tab(level) + "(" + var_prefix + i._nGlobalID + " ");
			dumpToTree(i._nHigh, var_prefix, ps, df, level + 1);
			dumpToTree(i._nLow, var_prefix, ps, df, level + 1);
			ps.print(") ");
		} else {
			ADDDNode d = (ADDDNode) cur;
			ps.print("(" + df.format(d._dLower) + ") ");
		}
	}
	
	public void dumpToTree(int n, Map names, PrintWriter ps,
			DecimalFormat df, int level) {

		ADDNode cur = getNode(n);

		if (cur instanceof ADDINode) {
			ADDINode i = (ADDINode) cur;
			ps.print("\n" + tab(level) + "(" + names.get(i._nGlobalID) + " ");
			dumpToTree(i._nHigh, names, ps, df, level + 1);
			dumpToTree(i._nLow, names, ps, df, level + 1);
			ps.print(") ");
		} else {
			ADDDNode d = (ADDDNode) cur;
			ps.print("(" + df.format(d._dLower) + ") ");
		}
	}

	public String tab(int len) {
		StringBuffer sb = new StringBuffer("   ");
		for (int i = 0; i < len; i++, sb.append("   "))
			;
		return sb.toString();
	}

	// //////////////////////////////////////////////////////////////
	// Miscellaneous methods
	// //////////////////////////////////////////////////////////////

	// A quick test to verify canonical order! Returns false if problem.
	public boolean verifyOrder(int id) {
		return verifyOrder(id, -1);
	}

	public boolean verifyOrder(int n, int par_gid) {
		if (n != 0) {
			ADDNode node = getNode(n);
			if (node instanceof ADDDNode) {
				return true;
			}
			ADDINode ni = (ADDINode) node;
			if (par_gid != -1) {
				// Verify order
				if (par_gid == ni._nGlobalID
						|| !comesBefore(par_gid, ni._nGlobalID)) {
					return false;
				}
			}
			return verifyOrder(ni._nLow, ni._nGlobalID)
					&& verifyOrder(ni._nHigh, ni._nGlobalID);
		} else {
			return true;
		}
	}

	public String toString() {

		StringBuffer sb = new StringBuffer();

		// Show order
		sb.append("Var order: " + _alOrder + "\n");
		// sb.append("Val range: " + procList(getValueRange()) + "\n");

		// Recurse from the root and show each branch
		sb.append("Structure:\n" + getNode(_nRoot).toString(this, 0) + "\n");

		return sb.toString();
	}

	public Graph getGraph(int id) {
		return getGraph(id, null);
	}

	public Graph getGraph(int id, Map id2var) {
		Graph g = new Graph(true /* directed */, false /* bottom-to-top */,
				            /*left-to-right*/ false, true /* multi-links */);
		getNode(id).toGraph(this, g);
		if (id2var != null)
			g.remap(id2var);
		return g;
	}

	public String printNode(int id) {
		return getNode(id).toString(this, 0);
	}

	public void pruneReport() {
		System.out.println("\nPrune Report:\n-------------");
		System.out.println("OR:   " + OR_PRUNE_CNT++);
		System.out.println("AND:  " + AND_PRUNE_CNT++);
		System.out.println("PROD: " + PROD_PRUNE_CNT++);
		System.out.println("MIN:  " + MIN_PRUNE_CNT++);
		System.out.println("MAX:  " + MAX_PRUNE_CNT++ + "\n");
	}

}
