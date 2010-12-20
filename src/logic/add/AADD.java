//////////////////////////////////////////////////////////////////////
//
// Algebraic Decision Diagram Package (Affine ADD - AADD)
//
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   6/1/04
//
// Notes:
// ------
// - Int appended to a method name can mean either the 'internal'
//   version or the version using integers... need to disambiguate
//   this sometime.
//
// TODO:
// -----
// 
//////////////////////////////////////////////////////////////////////

// TODO: Should be special case in Apply for sum of two linear functions
//       to ensure no blowup and reduce numerical precision error.
//
//       For approximate dynamic programming with LINEAR_PRUNING turned
//       off, would always permit largest prune to be a linear function,
//       which could be useful for a basis additive approximation.

package logic.add;

import graph.Graph;

import java.math.*;
import java.text.*;
import java.util.*;

/**
 * General class for implementation of AADD data structure
 **/
public class AADD extends DD {

	// Precision setting (1e-10 before change to deal with precision)
	public static final double PRECISION = 1e-10d;

	// Perform node merging?
	public static final boolean USE_NODE_MERGING = false;
	public static final boolean MERGE_IDENT_SUBNODES = true;

	// Print warning info?
	public static final boolean WARNING = false;

	// Print debug info?  (Should compile out otherwise.)
	public static boolean PRINT_DEBUG = false;
	public static boolean PRINT_REDUCE = false;
	public static boolean PRINT_APPLY = false;
	public static boolean DEBUG_PRUNE = false;

	// Internal statistics
	public static long APPLY_CALLS = 0;
	public static int TERM_PRUNE_CNT = 0;
	public static int PROD_PRUNE_CNT = 0;
	public static int MIN_PRUNE_CNT = 0;
	public static int MAX_PRUNE_CNT = 0;
	public static int SUM_CACHE_HITS = 0;
	public static int MAX_CACHE_HITS = 0;
	public static int PROD_CACHE_HITS = 0;
	public static int PRUNE_CACHE_HITS = 0;
	public static int REDUCE_CACHE_HITS = 0;
	public static int APPLY_CACHE_HITS = 0;
	public static int PRECISION_PRUNES = 0;
	public static int IDENT_PRUNES = 0;

	// Local data for AADD 
	public AADD _this = this; // For inner classes to access
	public AADDRNode _pRoot; // local id of root node
	public int _nINodeIDCnt; // counter for local ids
	public int _nRNodeIDCnt; // counter for local ids

	// Static node caches (id for ADDNode, 
	public HashMap _hmNodes; // maps ADDRNode(id) -> ADDNode (AADDINode or ADDDNode if id==0)
	public Map _hmINodeCache; // <gid, low rid, high rid> -> AADDINode
	public HashMap _hmRNodes; // maps ADDRNode(rid)       -> AADDRNode
	public ADDDNode _zeroDNode; // the terminal dnode (zero)

	// Reduce/apply/prune/special caches
	public Map _hmApplyCache; // cache for apply operation
	public HashMap _hmReduceMap; // maps <id> -> ADDNode (Reduce cache)
	public HashMap _hmReduceRemap; // maps <id> -> ADDNode (Reduce cache)
	public HashMap _hmPruneMap; // maps <id> -> ADDNode (Prune cache)

	public HashMap _hmNewNodes = null;
	public Map _hmNewINodeCache = null;
	public HashMap _hmNewRNodes = null;

	// Temp data
	public SAINodeIndex _tmpSAINode1 = new SAINodeIndex(INVALID, INVALID,
			INVALID, -1, -1, -1, -1);
	public SAINodeIndex _tmpSAINode2 = new SAINodeIndex(INVALID, INVALID,
			INVALID, -1, -1, -1, -1);
	public ADDRNode _tmpADDRNode = new ADDRNode(INVALID);

	//public int        _nWhich;      // For range-keeping 1 = min, 2 = max

	///////////////////////////////////////////////////////////////////
	//                    Basic and copy constructors
	///////////////////////////////////////////////////////////////////

	public AADD(ArrayList order) {

		_pRoot = null;
		_nINodeIDCnt = 1;
		_nRNodeIDCnt = 1;
		_alOrder = (ArrayList) order.clone();
		_hmGVarToLevel = new HashMap();

		// Caches
		_hmNodes = new HashMap();
		_hmRNodes = new HashMap();
		_hmPruneMap = new HashMap();
		_hmReduceMap = new HashMap();
		_hmReduceRemap = new HashMap();
		_hmApplyCache = USE_NODE_MERGING ? (Map) new TreeMap()
				: (Map) new HashMap();
		_hmINodeCache = USE_NODE_MERGING ? (Map) new TreeMap()
				: (Map) new HashMap();

		// Initialize zero node
		_zeroDNode = new ADDDNode(0, 0d, 0d);
		ADDRNode zero_ref = new ADDRNode(0);
		_hmNodes.put(zero_ref, _zeroDNode);
		//_nWhich         = 0;

		// Build map from global var to order level
		_hmGVarToLevel.clear();
		for (int i = 0; i < _alOrder.size(); i++) {
			_hmGVarToLevel.put((Integer) _alOrder.get(i), new Integer(i));
		}
	}

	public AADD(AADD src) {

		_nINodeIDCnt = 1;
		_nRNodeIDCnt = 1;

		// Caches
		_hmNodes = new HashMap();
		_hmRNodes = new HashMap();
		_hmPruneMap = new HashMap();
		_hmReduceMap = new HashMap();
		_hmReduceRemap = new HashMap();
		_hmApplyCache = USE_NODE_MERGING ? (Map) new TreeMap()
				: (Map) new HashMap();
		_hmINodeCache = USE_NODE_MERGING ? (Map) new TreeMap()
				: (Map) new HashMap();

		// Initialize zero node
		_zeroDNode = new ADDDNode(0, 0d, 0d);
		ADDRNode zero_ref = new ADDRNode(0);
		_hmNodes.put(zero_ref, _zeroDNode);
		//_nWhich      = 0;

		// Takes care of root, order, gvar_map, nodeLevel
		_alOrder = (ArrayList) src._alOrder.clone();
		_hmGVarToLevel = (HashMap) src._hmGVarToLevel.clone();

		// Copy over the node structure and load the caches
		setRoot(reduceRestrict(src._pRoot, src, -1, -1 /* Don't perform any op! */));
	}

	//////////////////////////////////////////////////////////////////
	//             Flushing and special node maintenance
	//////////////////////////////////////////////////////////////////

	// Flush caches but save special nodes.  Maybe could avoid
	// ADDRNode allocation with factory allocator?  Not sure how much
	// it would save.
	public void flushCaches(boolean print_info) {

		// Print starting info
		if (print_info) {
			System.out.print("[FLUSHING CACHES... ");
			//showCacheSize();
			ResetTimer();
		}

		// Can always clear these
		_hmApplyCache = USE_NODE_MERGING ? (Map) new TreeMap()
				: (Map) new HashMap();
		_hmReduceMap = new HashMap();
		_hmReduceRemap = new HashMap();
		_hmPruneMap = new HashMap();

		// Set up temporary alternates to these HashMaps
		_hmNewNodes = new HashMap();
		_hmNewRNodes = new HashMap();
		_hmNewINodeCache = USE_NODE_MERGING ? (Map) new TreeMap()
				: (Map) new HashMap();

		// Copy over 'special' nodes then set new maps
		Iterator i = _hsSpecialNodes.iterator();
		while (i.hasNext()) {
			cacheRNode((ADDRNode) i.next());
		}
		_hmNodes = _hmNewNodes;
		_hmRNodes = _hmNewRNodes;
		_hmINodeCache = _hmNewINodeCache;

		// Copy over the special zero ADDDNode
		ADDRNode zero_ref = new ADDRNode(0);
		_hmNodes.put(zero_ref, _zeroDNode);

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
		} // Print starting info
	}

	public void cacheINode(ADDRNode r) {
		if (r._lid == 0 || _hmNewNodes.containsKey(r)) {
			return;
		}
		AADDINode ni = (AADDINode) _hmNodes.get(r);
		_hmNewNodes.put(r, ni);
		_hmNewINodeCache.put(new SAINodeIndex(ni._nGlobalID, ni._nLow,
				ni._nHigh, ni._dLowOffset, ni._dLowMult, ni._dHighOffset,
				ni._dHighMult), r);
		cacheINode(new ADDRNode(ni._nLow));
		cacheINode(new ADDRNode(ni._nHigh));
	}

	public void cacheRNode(ADDRNode r) {
		AADDRNode n = (AADDRNode) _hmRNodes.get(r);
		_hmNewRNodes.put(r, n);
		cacheINode(new ADDRNode(n._nRefID));
	}

	//////////////////////////////////////////////////////////////////
	//              Internal data structure maintenance
	//////////////////////////////////////////////////////////////////

	// Quick cache snapshot
	public void showCacheSize() {
		System.out.println("APPLY CACHE:  " + _hmApplyCache.size());
		System.out.println("REDUCE CACHE: " + _hmReduceMap.size());
		System.out.println("INODE CACHE:  " + _hmINodeCache.size());
		System.out.println("RNODE CACHE:  " + _hmRNodes.size() + "\n");
	}

	// Total cache snapshot
	public long getCacheSize() {
		return _hmApplyCache.size() + _hmReduceMap.size()
				+ _hmINodeCache.size() + _hmRNodes.size();
	}

	// An exact count for the AADD rooted at _pRoot
	public long countExactNodesFromINode(int iid) {
		HashSet cset = new HashSet();
		countExactNodesInt(cset, iid);
		return cset.size();
	}

	public long countExactNodes(int rid) {
		HashSet cset = new HashSet();
		countExactNodesInt(cset, getRNode(rid)._nRefID);
		return cset.size();
	}

	public Set getExactNodes(int rid) {
		HashSet cset = new HashSet();
		countExactNodesInt(cset, getRNode(rid)._nRefID);
		return cset;
	}

	public void countExactNodesInt(HashSet cset, int id) {
		Integer iid = new Integer(id);
		if (cset.contains(iid)) {
			return;
		}
		cset.add(iid);
		ADDNode n = getNode(id);
		if (n instanceof AADDINode) {
			countExactNodesInt(cset, ((AADDINode) n)._nLow);
			countExactNodesInt(cset, ((AADDINode) n)._nHigh);
		}
	}

	public Set getGIDs(int id) {
		HashSet cset = new HashSet();
		HashSet gset = new HashSet();
		collectGIDsInt(cset, gset, getRNode(id)._nRefID);
		return gset;
	}

	public void collectGIDsInt(HashSet cset, HashSet gset, int id) {
		Integer iid = new Integer(id);
		if (cset.contains(iid)) {
			return;
		}
		cset.add(iid);
		ADDNode n = getNode(id);
		if (n instanceof AADDINode) {
			gset.add(new Integer(((AADDINode) n)._nGlobalID));
			collectGIDsInt(cset, gset, ((AADDINode) n)._nLow);
			collectGIDsInt(cset, gset, ((AADDINode) n)._nHigh);
		}
	}

	//////////////////////////////////////////////////////////////////
	//                         Node retrieval
	//////////////////////////////////////////////////////////////////

	// Set the root node and update ref counts
	public void setRoot(AADDRNode r) {
		_pRoot = r;
	}

	// The only way to retrieve an AADDINode from an ID (returns ADDDNode if 0)
	public ADDNode getNode(int local_id) {
		if (local_id >= 0 && local_id < _nINodeIDCnt) {
			_tmpADDRNode.set(local_id);
			return (ADDNode) _hmNodes.get(_tmpADDRNode);
		} else {
			System.out.println("AADD.getINode: Error invalid local id: "
					+ local_id + ", >= " + _nINodeIDCnt);
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace(System.out);
			}
			System.exit(1);
			return null;
		}
	}

	// Returns rid for node
	public int addRNodeRef(AADDRNode r) {

		int rid = _nRNodeIDCnt++;
		ADDRNode ref = new ADDRNode(rid);
		_hmRNodes.put(ref, r);

		return rid;
	}

	// The only way to retrieve an AADDRNode from an ID 
	// Note: Different id space!
	public AADDRNode getRNode(int rid) {
		if (rid >= 0 && rid < _nRNodeIDCnt) {
			_tmpADDRNode.set(rid);
			return (AADDRNode) _hmRNodes.get(_tmpADDRNode);
		} else {
			System.out.println("AADD.getRNode: Error invalid local id" + rid
					+ ", >= " + _nRNodeIDCnt);
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace(System.out);
			}
			System.exit(1);
			return null;
		}
	}

	// Returns local id for inode
	public int createINode(int gid, int low, int high, double o_l, double m_l,
			double o_h, double m_h) {

		//System.out.println("Create: <" + gid + "," + low + "," + high + ">  ->  " + _nRefIDCnt);
		int lid = _nINodeIDCnt++;
		ADDRNode ref = new ADDRNode(lid);
		AADDINode n = new AADDINode(lid, gid, low, high, o_l, m_l, o_h, m_h);

		_hmNodes.put(ref, n);
		_hmINodeCache.put(new SAINodeIndex(gid, low, high, o_l, m_l, o_h, m_h),
				ref);

		return lid;
	}

	// This actually does low==high simplification in place... very
	// important to ensure ref counts ok since double linking screws
	// things up.  WARNING: May not return INode if low==high.  
	//
	// This method does normalization in place.
	public AADDRNode getINode(int gid, int low, int high, double o_l,
			double m_l, double o_h, double m_h, boolean create) {

		AADDRNode ret = null;

		// First remove 0.0 multipliers and replace with the zero node
		if (m_l <= PRECISION) {
			low = 0;
		}
		if (m_h <= PRECISION) {
			high = 0;
		}

		if (MERGE_IDENT_SUBNODES) {
			// Test to see if low and high should be merged into
			// same node
			ADDNode low_n  = (ADDNode)getNode(low);
			ADDNode high_n = (ADDNode)getNode(high);
			
			if ((low_n instanceof AADDINode) && (high_n instanceof AADDINode)) {
				
				AADDINode low_ni  = (AADDINode)low_n;
				AADDINode high_ni = (AADDINode)high_n;
				
				/*
				System.out.println("Checking " + low_n._nLocalID + " :: " + 
						high_n._nLocalID + " for merge");
				System.out.println(low_ni._nHigh  + " == " + high_ni._nHigh + 
						", " + low_ni._nLow + " == " + high_ni._nLow);
				System.out.println(Math.abs(low_ni._dHighMult - high_ni._dHighMult));
				System.out.println(Math.abs(low_ni._dHighOffset - high_ni._dHighOffset));
				System.out.println(Math.abs(low_ni._dLowMult - high_ni._dLowMult));
				System.out.println(Math.abs(low_ni._dLowOffset - high_ni._dLowOffset));
				*/

				if (low_ni._nLocalID != high_ni._nLocalID &&
					low_ni._nHigh == high_ni._nHigh &&
					low_ni._nLow  == high_ni._nLow &&
					Math.abs(low_ni._dHighMult - high_ni._dHighMult) <= PRECISION &&
					Math.abs(low_ni._dHighOffset - high_ni._dHighOffset) <= PRECISION &&
					Math.abs(low_ni._dLowMult - high_ni._dLowMult) <= PRECISION &&
					Math.abs(low_ni._dLowOffset - high_ni._dLowOffset) <= PRECISION) {
					
					//System.out.println("MERGE!");
					//System.exit(1);
					low = high;
				}
				
			}
		}
		
		// First check if low == high... in this case, just perform the
		// obvious equivalent reduction 
		if (low == high && Math.abs(o_l - o_h) <= PRECISION
				&& Math.abs(m_l - m_h) <= PRECISION) {

			ret = new AADDRNode(low, o_l, m_l);

			// **Must deal with numerical precision error**
			if ((ret != null) && (ret._nRefID != 0)
					&& (ret._dMult <= PRECISION)) {
				//System.out.println(ret.toString(this, 0));
				if (WARNING) {
					System.out.println("WARNING: Mult near 0 in getINode()");
				}
				//System.out.println("WARNING: Mult near 0 in getINode()");
				//System.exit(1);
				ret = new AADDRNode(0, ret._dOffset, 0.0d);
			}

		} else {

			// Now compute normalization
			double r_min = Math.min(o_l, o_h);
			double r_max = Math.max(o_l + m_l, o_h + m_h);
			double r_range = (r_max - r_min);// * 1d/(1 << (Integer)_hmGVarToLevel.get(gid));
			o_l = (o_l - r_min) / r_range;
			o_h = (o_h - r_min) / r_range;
			m_l = m_l / r_range;
			m_h = m_h / r_range;

			// **Must deal with numerical precision error**
			if (r_range <= PRECISION) {

				// Don't need to make an INode here...
				if (WARNING) {
					System.out.println("WARNING: Mult near 0 in getINode()");
				}
				//System.exit(1);
				ret = new AADDRNode(0, r_min, 0.0d);

			} else {

				if (USE_NODE_MERGING) {

					// We're trying to index R, want to see if it has a nearest neighbor

					// Get a submap from the node cache
					_tmpSAINode1 = new SAINodeIndex(gid, low, high, o_l, m_l,
							o_h, m_h, -2d * PRECISION);
					_tmpSAINode2 = new SAINodeIndex(gid, low, high, o_l, m_l,
							o_h, m_h, 2d * PRECISION);
					Map submap = ((TreeMap) _hmINodeCache).subMap(_tmpSAINode1,
							_tmpSAINode2);

					Iterator i = submap.entrySet().iterator();
					while (i.hasNext()) {
						Map.Entry me = (Map.Entry) i.next();
						SAINodeIndex s = (SAINodeIndex) me.getKey();

						// Do actual range comparison to see if nearest neighbor
						if (Math.abs(o_l - s._dOffset1) <= PRECISION
								&& Math.abs(m_l - s._dMult1) <= PRECISION
								&& Math.abs(o_h - s._dOffset2) <= PRECISION
								&& Math.abs(m_h - s._dMult2) <= PRECISION) {

							// Match found!!!
							ret = new AADDRNode(
									((ADDRNode) me.getValue())._lid, r_min,
									r_range);
							break;
						}
					}

					// No match found so have to create a new INode
					if (ret == null) {
						//System.out.println("Match not found...");
						ret = new AADDRNode(createINode(gid, low, high, o_l,
								m_l, o_h, m_h), r_min, r_range);
					}

				} else {
										
					_tmpSAINode1.set(gid, low, high, o_l, m_l, o_h, m_h);
					ADDRNode ref = (ADDRNode) _hmINodeCache.get(_tmpSAINode1);
					if (ref != null) {
						ret = new AADDRNode(ref._lid, r_min, r_range);
					} else if (create) {
						ret = new AADDRNode(createINode(gid, low, high, o_l,
								m_l, o_h, m_h), r_min, r_range);
					}
				}
			}
		}

		return ret;
	}

	public AADDRNode getDNode(double val, boolean create) {
		return new AADDRNode(0, val, 0.0d);
	}

	/////////////////////////////////////////////////////////////////
	//                 General ADD / Unary Operations
	/////////////////////////////////////////////////////////////////

	public double getMaxValue() {
		return _pRoot._dOffset + _pRoot._dMult;
	}

	public double getMinValue() {
		return _pRoot._dOffset;
	}

	public double getMaxValue(int id) {
		AADDRNode r = getRNode(id);
		return r._dOffset + r._dMult;
	}

	public double getMinValue(int id) {
		AADDRNode r = getRNode(id);
		return r._dOffset;
	}

	// Gets *canonical* AADDRNode ref to return
	public int scalarMultiply(int id, double val) {
		AADDRNode r = getRNode(id);
		AADDRNode ret = scalarMultiply(r, val);
		return addRNodeRef(ret);
	}

	// Produces new AADD.
	public AADD scalarMultiply(double val) {
		AADD a1 = new AADD(_alOrder);
		AADDRNode aval = a1.getDNode(val, true);
		a1.setRoot(aval);
		return Apply(a1, this, ARITH_PROD);
	}

	// Within current AADD.
	public AADDRNode scalarMultiply(AADDRNode r, double val) {

		if (r._nRefID == 0) {
			return getDNode(r._dOffset * val, true);
		} else if (val == 0d) {
			PROD_PRUNE_CNT++;
			return new AADDRNode(0, 0d, 0d);
		} else if (val > 0d) {
			PROD_PRUNE_CNT++;
			return new AADDRNode(r._nRefID, val * r._dOffset, val * r._dMult);
		}

		// Otherwise we'll have to call Apply
		AADDRNode aval = getDNode(val, true);
		return applyInt(aval, r, ARITH_PROD);
	}

	// Gets *canonical* AADDRNode ref to return
	public int scalarAdd(int id, double val) {
		AADDRNode r = getRNode(id);
		AADDRNode ret = scalarAdd(r, val);
		return addRNodeRef(ret);
	}

	public AADD scalarAdd(double val) {
		AADD new_aadd = new AADD(this);
		new_aadd._pRoot._dOffset += val;
		return new_aadd;
	}

	public AADDRNode scalarAdd(AADDRNode r, double val) {
		return new AADDRNode(r._nRefID, r._dOffset + val, r._dMult);
	}

	// These are harder to do in place because inversion must change
	// the base/inode values... so have to do an Apply operation with the
	// ARITH_MINUS/DIV operator.  There may be an efficient way around this
	// but it is not clear to me at this point.

	public AADD negate() {
		AADD a1 = new AADD(_alOrder);
		AADDRNode zero = a1.getDNode(0.0d, true);
		a1.setRoot(zero);
		return Apply(a1, this, ARITH_MINUS);
	}

	// Within current AADD, gets *canonical* AADDRNode ref to return
	public int negate(int rid) {
		AADDRNode zero = getDNode(0d, true);
		AADDRNode ret = applyInt(zero, getRNode(rid), ARITH_MINUS);
		return addRNodeRef(ret);
	}

	public AADD invert() {
		AADD a1 = new AADD(_alOrder);
		AADDRNode one = a1.getDNode(1.0d, true);
		a1.setRoot(one);
		return Apply(a1, this, ARITH_DIV);
	}

	// Within current AADD, gets *canonical* AADDRNode ref to return
	public int invert(int rid) {
		AADDRNode one = getDNode(1d, true);
		AADDRNode ret = applyInt(one, getRNode(rid), ARITH_DIV);
		return addRNodeRef(ret);
	}

	///////////////////////////////////////////////////////////////////////////
	//                         Approximation Algorithms
	///////////////////////////////////////////////////////////////////////////

	// Prune and return canonical reference
	public int pruneNodes(int rid) {

		// Relevant vars here are PRUNE_TYPE and PRUNE_PRECISION
		if (PRUNE_TYPE == NO_REPLACE || PRUNE_PRECISION <= 0d)
			return rid;

		AADDRNode root = getRNode(rid);
		PruneResultMap prm = pruneNodeDiff2(root, PRUNE_PRECISION); 
	
		//System.out.println("  - used error: " + _df.format(PRUNE_PRECISION - prm._dAllowErr) + " / " + _df.format(PRUNE_PRECISION)); 
		AADDRNode new_root = reduceRemap(root, prm._hmRemap);
		return addRNodeRef(new_root);
	}

	// Start at root
	public void pruneNodeDiff() {
		setRoot(getRNode(pruneNodes(_pRoot._nRefID)));
	}

	public static class PruneResultMap {
		HashMap<Integer,Integer> _hmRemap = null;
		double _dAllowErr = 0d;
		PruneResultMap(AADDRNode rnode, double err) {
			_hmRemap = new HashMap<Integer,Integer>();
			_dAllowErr = 0d;
		}
	}

	public class PruneResult {
		AADDRNode _rnode = null;
		double    _allow_err = 0d;
		PruneResult(AADDRNode rnode, double err) {
			_rnode = rnode;
			_allow_err = err;
		}
	}

	public class PruneData {
		AADDINode _node     = null;
		double _dMaxImpact  = 0d;
		double _dErrorAllow = 0d;
		boolean _bVisited = false;
		public PruneData(AADDINode n, double max_impact, double error_allow) {
			_node = n;
			_dMaxImpact = max_impact;
			_dErrorAllow = error_allow;
		}
		public String toString() {
			if (_node == null)
				return "[ ZERO ]";
			else
				return _node.toStringLocal(_this) + 
				   "\nMax impact:  " + _df.format(_dMaxImpact) +
				   "\nError allow: " + _df.format(_dErrorAllow);
		}
	}
	
	public static void EnsureSpace(ArrayList<TreeMap<Integer,PruneData>> pdata, int index) {
		if (pdata.size() <= index)
			for (int i = pdata.size(); i <= index; i++)
				pdata.add(new TreeMap<Integer,PruneData>());
	}
	
	public PruneData pd_zero = null;
	
	public void getPruneDataMap(ArrayList<TreeMap<Integer,PruneData>> pdata,
			HashSet<Integer> cset, int id, double range, double allow_error) {
		if (cset.contains(id)) {
			return;
		}
		cset.add(id);
		ADDNode n = getNode(id);
		if (n instanceof AADDINode) {
			AADDINode ni = ((AADDINode) n); 
			int var = ni._nGlobalID;
			int level = (Integer)_hmGVarToLevel.get(var);
			EnsureSpace(pdata, level);
			pdata.get(level).put(ni._nLocalID, new PruneData(ni, range, allow_error));
			getPruneDataMap(pdata, cset, ni._nLow, ni._dLowMult * range, allow_error);
			getPruneDataMap(pdata, cset, ni._nHigh, ni._dHighMult * range, allow_error);
		}
		pd_zero = new PruneData(null, 0d, allow_error);
	}
	
	public int getRemappedNodeID(int id, HashMap<Integer,Integer> remap) {
		Integer remap_id = null;
		while ((remap_id = remap.get(id)) != null)
			id = remap_id;
		return id;
	}
	
	public PruneData getPruneData(ArrayList<TreeMap<Integer,PruneData>> pdata, int id) {
		ADDNode n = getNode(id);
		if (n instanceof AADDINode) {
			AADDINode ni = (AADDINode)getNode(id);
			int var = ni._nGlobalID;
			int level = (Integer)_hmGVarToLevel.get(var);
			EnsureSpace(pdata, level);
			return pdata.get(level).get(ni._nLocalID);
		} else
			return pd_zero;
	}
	
	public PruneResultMap pruneNodeDiff(AADDRNode r, double allow_error) {
		
		// Collect all nodes in this AADD and store them in an array of arrays 
		// by var level
		//
		// For each node, observe the max impact that it has on subnodes
		ArrayList<TreeMap<Integer,PruneData>> pdata = new ArrayList<TreeMap<Integer,PruneData>>();
		getPruneDataMap(pdata, new HashSet<Integer>(), r._nRefID, r._dMult, allow_error);
		
		// For level = bottom -> level = top
		// - Go through nodes in order... find all that can match within
		//   an epsilon error bound... perform a merge and note the maximum
		//   error for that merge... errors accumulate from children
		//
		//   Just maintain a "remap" cache and do lookups in this cache
		PruneResultMap prm = new PruneResultMap(r, 0d);
		ArrayList<PruneData> nodes_merge = new ArrayList<PruneData>();
		
		ArrayList<PruneData> new_pds = new ArrayList<PruneData>();
		int last_level = -1;
		for (int level = pdata.size() - 1; level >= 0; level--) {
			TreeMap<Integer,PruneData> level_pdata = pdata.get(level);

			if (last_level != -1)
				for (PruneData new_pd : new_pds) {
					pdata.get(last_level).put(new_pd._node._nLocalID, new_pd);
				}
			new_pds.clear();
			last_level = level;
			
			for (Map.Entry<Integer, PruneData> me : level_pdata.entrySet()) {

				PruneData pd = level_pdata.get(me.getKey());
				if (pd._bVisited) 
					continue;
				pd._bVisited = true;
				int nlow   = getRemappedNodeID(pd._node._nLow, prm._hmRemap);
				int nhigh  = getRemappedNodeID(pd._node._nHigh, prm._hmRemap);
				PruneData pd_low  = getPruneData(pdata, nlow);
				PruneData pd_high = getPruneData(pdata, nhigh);
				
				// Set current allowable error to min allowable error of subnodes
				pd._dErrorAllow = Math.min( pd_low._dErrorAllow, pd_high._dErrorAllow );

				if (DEBUG_PRUNE) 
					System.out.println("CHECKING: Level " + level + ", #" + pd._node._nLocalID + ": " + pd);
					
				// If not, determine which other nodes to merge in with
				// it... let this be the canonical node representation for now
				nodes_merge.clear();
				
				double accum_low_offset  = pd._node._dLowOffset;
				double accum_high_offset = pd._node._dHighOffset;
				double accum_low_mult    = pd._node._dLowMult;
				double accum_high_mult   = pd._node._dHighMult;
				
				for (Map.Entry<Integer, PruneData> me2 : level_pdata.entrySet()) {
			
					PruneData pd2 = level_pdata.get(me2.getKey());
					if (pd2._bVisited) 
						continue;
		
					int nlow2  = getRemappedNodeID(pd2._node._nLow, prm._hmRemap);
					int nhigh2 = getRemappedNodeID(pd2._node._nHigh, prm._hmRemap);
					PruneData pd2_low  = getPruneData(pdata, nlow);
					PruneData pd2_high = getPruneData(pdata, nhigh);
					pd2._dErrorAllow = Math.min( pd2_low._dErrorAllow, pd2_high._dErrorAllow );

					if (nlow == nlow2 && nhigh == nhigh2) {
						
						// Look at pd as well since it will actually migrate towards
						// pd2 after average
						double max_impact = Math.max( pd._dMaxImpact, pd2._dMaxImpact );
						double merge_error = 2d * max_impact *
							Math.max( Math.abs(pd._node._dLowOffset  - pd2._node._dLowOffset) +
									  Math.abs(pd._node._dLowMult    - pd2._node._dLowMult),
									  Math.abs(pd._node._dHighOffset - pd2._node._dHighOffset) +
									  Math.abs(pd._node._dHighMult   - pd2._node._dHighMult) );

						// Look at error impact on both nodes... migrating either way
						double remaining_error = Math.min(pd._dErrorAllow, pd2._dErrorAllow) - merge_error;
						if (remaining_error > 0d) {
							accum_low_offset  += pd2._node._dLowOffset;
							accum_high_offset += pd2._node._dHighOffset;
							accum_low_mult    += pd2._node._dLowMult;
							accum_high_mult   += pd2._node._dHighMult;
							if (DEBUG_PRUNE) System.out.println("** MERGING IN: [" + _df.format(remaining_error) 
									+ "]\n" + pd2 + "\n-->" + pd);
							nodes_merge.add(pd2);
						}
					}
					
				}
				
				// Go through all merges and record the maximum error induced
				// Remap the ids and mark remaps as visited
				if (nodes_merge.size() > 0) {
					nodes_merge.add(pd);
					accum_low_offset  /= (double)(nodes_merge.size());
					accum_high_offset /= (double)(nodes_merge.size());
					accum_low_mult    /= (double)(nodes_merge.size());
					accum_high_mult   /= (double)(nodes_merge.size());
					int new_node = createINode(pd._node._nGlobalID, 
							nlow, nlow, accum_low_offset, accum_low_mult, accum_high_offset, accum_high_mult);
					AADDINode new_inode = (AADDINode)getNode(new_node);
					//error_prune = Math.max(, b)
	
					// Prune data here?
					PruneData new_pdata = new PruneData(new_inode, 
							/* impact */ 0d, /* error */ Double.MAX_VALUE);

					new_pdata._bVisited = true;
					if (DEBUG_PRUNE) 
						System.out.println("** MIGRATING: [" + _df.format(pd._dErrorAllow) + 
							"] \n" + pd + "\n" + new_pdata);
					new_pds.add(new_pdata);
					pd = new_pdata;
	
					for (int index = 0; index < nodes_merge.size(); index++) {
						
						PruneData to_merge = nodes_merge.get(index);
						pd._dMaxImpact = Math.max( pd._dMaxImpact, to_merge._dMaxImpact );
						double merge_error = to_merge._dMaxImpact *
							Math.max( Math.abs(to_merge._node._dLowOffset - accum_low_offset) +
									  Math.abs(to_merge._node._dLowMult - accum_low_mult),
									  Math.abs(to_merge._node._dHighOffset - accum_high_offset) +
									  Math.abs(to_merge._node._dHighMult - accum_high_mult) );
						
						pd._dErrorAllow = Math.min(pd._dErrorAllow, to_merge._dErrorAllow - merge_error);
						//if (pd._dErrorAllow > 0d) {
						//	System.out.println("Overshot error bound: " + index + " / ")
						//}
						prm._hmRemap.put(to_merge._node._nLocalID, pd._node._nLocalID);
						to_merge._bVisited = true;
					}
				}
				
				// Determine whether pd itself should be remapped
				if (nhigh == nlow) {
					double error_prune = pd._dMaxImpact *
						( Math.abs(pd._node._dHighMult - pd._node._dLowMult) + 
						  Math.abs(pd._node._dHighOffset - pd._node._dLowOffset) )/2d;
					
					double error_remain = pd._dErrorAllow - error_prune;
					if (error_remain > 0d) {

						// Visited is already marked
						
						// Replace this node with a new node with identical
						// multiplier and offset... it will be removed during reduce
						double offset = (pd._node._dLowOffset + pd._node._dHighOffset)/2d;
						double mult   = (pd._node._dLowMult   + pd._node._dHighMult)/2d;;
						int new_node = createINode(pd._node._nGlobalID, 
								nlow, nlow, offset, mult, offset, mult);
						AADDINode new_inode = (AADDINode)getNode(new_node);
						//error_prune = Math.max(, b)

						// Prune data here?
						prm._hmRemap.put(pd._node._nLocalID, new_node);
						PruneData new_pdata = new PruneData(new_inode, pd._dMaxImpact, error_remain);
						new_pdata._bVisited = true;
						if (DEBUG_PRUNE) 
							System.out.println("** PRUNING: [" + _df.format(error_remain) + 
								"] \n" + pd + "\n" + new_pdata);
						new_pds.add(new_pdata);
						
					}
				}
			}
			
		}
		
		// Call reduce with the remap cache
		//try { System.in.read();} catch (Exception e) {}
		
		// Set the final error and return
		prm._dAllowErr = getPruneData(pdata, getRemappedNodeID(r._nRefID, prm._hmRemap))._dErrorAllow;
		return prm;
	}
	
	public PruneResultMap pruneNodeDiff2(AADDRNode r, double allow_error) {
		
		// Collect all nodes in this AADD and store them in an array of arrays 
		// by var level
		//
		// For each node, observe the max impact that it has on subnodes
		ArrayList<TreeMap<Integer,PruneData>> pdata = new ArrayList<TreeMap<Integer,PruneData>>();
		getPruneDataMap(pdata, new HashSet<Integer>(), r._nRefID, r._dMult, allow_error);
		
		// For level = bottom -> level = top
		// - Go through nodes in order... find all that can match within
		//   an epsilon error bound... perform a merge and note the maximum
		//   error for that merge... errors accumulate from children
		//
		//   Just maintain a "remap" cache and do lookups in this cache
		PruneResultMap prm = new PruneResultMap(r, 0d);
		ArrayList<PruneData> nodes_merge = new ArrayList<PruneData>();
		ArrayList<Double>    error_merge = new ArrayList<Double>();
		
		ArrayList<PruneData> new_pds = new ArrayList<PruneData>();
		int last_level = -1;
		for (int level = pdata.size() - 1; level >= 0; level--) {
			TreeMap<Integer,PruneData> level_pdata = pdata.get(level);

			if (last_level != -1)
				for (PruneData new_pd : new_pds) {
					pdata.get(last_level).put(new_pd._node._nLocalID, new_pd);
				}
			new_pds.clear();
			last_level = level;
			
			for (Map.Entry<Integer, PruneData> me : level_pdata.entrySet()) {

				PruneData pd = level_pdata.get(me.getKey());
				if (pd._bVisited) 
					continue;
				pd._bVisited = true;
				int nlow   = getRemappedNodeID(pd._node._nLow, prm._hmRemap);
				int nhigh  = getRemappedNodeID(pd._node._nHigh, prm._hmRemap);
				PruneData pd_low  = getPruneData(pdata, nlow);
				PruneData pd_high = getPruneData(pdata, nhigh);
				
				// Set current allowable error to min allowable error of subnodes
				pd._dErrorAllow = Math.min( pd_low._dErrorAllow, pd_high._dErrorAllow );

				if (DEBUG_PRUNE) 
					System.out.println("CHECKING: Level " + level + ", #" + pd._node._nLocalID + ": " + pd);
					
				// If not, determine which other nodes to merge in with
				// it... let this be the canonical node representation for now
				nodes_merge.clear();
				
				for (Map.Entry<Integer, PruneData> me2 : level_pdata.entrySet()) {
			
					PruneData pd2 = level_pdata.get(me2.getKey());
					if (pd2._bVisited) 
						continue;
		
					int nlow2  = getRemappedNodeID(pd2._node._nLow, prm._hmRemap);
					int nhigh2 = getRemappedNodeID(pd2._node._nHigh, prm._hmRemap);
					PruneData pd2_low  = getPruneData(pdata, nlow);
					PruneData pd2_high = getPruneData(pdata, nhigh);
					pd2._dErrorAllow = Math.min( pd2_low._dErrorAllow, pd2_high._dErrorAllow );

					if (nlow == nlow2 && nhigh == nhigh2) {
						
						// Look at pd as well since it will actually migrate towards
						// pd2 after average
						double max_impact = Math.max( pd._dMaxImpact, pd2._dMaxImpact );
						double merge_error = max_impact *
							Math.max( Math.abs(pd._node._dLowOffset  - pd2._node._dLowOffset) +
									  Math.abs(pd._node._dLowMult    - pd2._node._dLowMult),
									  Math.abs(pd._node._dHighOffset - pd2._node._dHighOffset) +
									  Math.abs(pd._node._dHighMult   - pd2._node._dHighMult) );

						// Look at error impact on both nodes... migrating either way
						double remaining_error = Math.min(pd._dErrorAllow, pd2._dErrorAllow) - merge_error;
						if (remaining_error > 0d) {
							if (DEBUG_PRUNE) System.out.println("** MERGING IN: [" + _df.format(remaining_error) 
									+ "]\n" + pd2 + "\n-->" + pd);
							nodes_merge.add(pd2);
							error_merge.add(remaining_error);
						}
					}
					
				}
				
				// Go through all merges and record the maximum error induced
				// Remap the ids and mark remaps as visited
				if (nodes_merge.size() > 0) {

					if (DEBUG_PRUNE) 
						System.out.println("** MIGRATING: [" + _df.format(pd._dErrorAllow) + 
							"] \n" + pd + "\n" + pd);
	
					for (int index = 0; index < nodes_merge.size(); index++) {
						PruneData to_merge = nodes_merge.get(index);
						pd._dMaxImpact = Math.max( pd._dMaxImpact, to_merge._dMaxImpact );					
						pd._dErrorAllow = Math.min(pd._dErrorAllow, error_merge.get(index));
						prm._hmRemap.put(to_merge._node._nLocalID, pd._node._nLocalID);
						to_merge._bVisited = true;
					}
				}
				
				// Determine whether pd itself should be collapsed
				// TODO: include or not (set false)
				if (/*false &&*/ nhigh == nlow) {
					double error_prune = pd._dMaxImpact *
						( Math.abs(pd._node._dHighMult - pd._node._dLowMult) + 
						  Math.abs(pd._node._dHighOffset - pd._node._dLowOffset) )/2d;
					
					double error_remain = pd._dErrorAllow - error_prune;
					if (error_remain > 0d) {

						// Visited is already marked
						
						// Replace this node with a new node with identical
						// multiplier and offset... it will be removed during reduce
						double offset = (pd._node._dLowOffset + pd._node._dHighOffset)/2d;
						double mult   = (pd._node._dLowMult   + pd._node._dHighMult)/2d;;
						int new_node = createINode(pd._node._nGlobalID, 
								nlow, nlow, offset, mult, offset, mult);
						AADDINode new_inode = (AADDINode)getNode(new_node);
						//error_prune = Math.max(, b)

						// Prune data here?
						prm._hmRemap.put(pd._node._nLocalID, new_node);
						PruneData new_pdata = new PruneData(new_inode, pd._dMaxImpact, error_remain);
						new_pdata._bVisited = true;
						if (DEBUG_PRUNE) 
							System.out.println("** PRUNING: [" + _df.format(error_remain) + 
								"] \n" + pd + "\n" + new_pdata);
						new_pds.add(new_pdata);
						
					}
				}
			}
			
		}
		
		// Call reduce with the remap cache
		//try { System.in.read();} catch (Exception e) {}
		
		// Set the final error and return
		prm._dAllowErr = getPruneData(pdata, getRemappedNodeID(r._nRefID, prm._hmRemap))._dErrorAllow;
		return prm;
	}
	
	public final static boolean ALLOW_RANGE_PRUNE = false; // Seems to allow blowup sometimes
	public final static boolean ALLOW_LINEAR_PRUNE = true;
	
	// Prunes all node structure having impact less than prune_precision.
	// Range included because need a measure of the range induced by the
	// error at the node.
	public PruneResult pruneNodeDiffOld(AADDRNode r, double range, boolean recurse, double allow_error) {

		//System.out.println("ENTERING " + r._nRefID + " with allowable error: " + allow_error);
		
		// Can immediately check for local ID of 0 OR inability to prune 
		if (r._nRefID == 0 || allow_error <= 0d) {
			return new PruneResult(r, allow_error);
		}
		
		range *= r._dMult;

		// Check cache
		PruneResult ret = new PruneResult(null, allow_error);
		_tmpADDRNode.set(r._nRefID);
		if ((ret._rnode = (AADDRNode) _hmPruneMap.get(_tmpADDRNode)) == null) {

			// DANGER: SEEMS TO ALLOW BLOWUP
			if (ALLOW_RANGE_PRUNE && range <= allow_error) {

				// This entire subtree has impact less than PRUNE_PRECISION
				PruneResult retp = null;
				switch (PRUNE_TYPE) {
				case NO_REPLACE:
				case REPLACE_LOW:
				case REPLACE_HIGH: {
				}
					break;
				case REPLACE_MIN: {
					PRECISION_PRUNES++;
					retp = new PruneResult(getDNode(r._dOffset, true), allow_error - range);
				} break;
				case REPLACE_MAX: {
					PRECISION_PRUNES++;
					retp = new PruneResult(getDNode(r._dOffset + r._dMult, true), allow_error - range);
				} break;
				case REPLACE_AVG: {
					PRECISION_PRUNES++;
					retp = new PruneResult(getDNode((r._dOffset + r._dMult) / 2d, true), allow_error - range);
				} break;
				default: {
					System.out.println("Illegal replacement type " + PRUNE_TYPE);
					System.exit(1);
				} break;
				}
				
				if (retp != null) {
					_hmPruneMap.put(new ADDRNode(r._nRefID), retp._rnode);				
					return retp;
				}
			}
			
			// Not in cache, perform reduction on this AADDINode
			AADDINode ni = (AADDINode) getNode(r._nRefID);

			// Get high and low branches for this INode
			AADDRNode low = new AADDRNode(ni._nLow, ni._dLowOffset,
					ni._dLowMult);
			AADDRNode high = new AADDRNode(ni._nHigh, ni._dHighOffset,
					ni._dHighMult);
			
			// Recurse
			if (recurse) {
				PruneResult lowp  = pruneNodeDiffOld(low, range, true, ret._allow_err);
				low = lowp._rnode;
				PruneResult highp = pruneNodeDiffOld(high, range, true, ret._allow_err);
				high = highp._rnode;
				ret._allow_err = Math.min(lowp._allow_err, highp._allow_err);
				//System.out.println("- INITIAL RECURSION " + r._nRefID + " with allowable error: " + ret._allow_err);
			}

			// Should we prune?
			if (ALLOW_LINEAR_PRUNE && (low._nRefID == high._nRefID)) {
				
					double approx_err = range *
						(Math.abs(low._dOffset - high._dOffset) + 
						 Math.abs(low._dMult - high._dMult));
				
					// TODO: use single c, b... then error is range*c_err + range*b_err
					
					// This entire subtree has impact less than PRUNE_PRECISION
					PruneResult retp = null;
					if (approx_err < ret._allow_err) {
						
						//System.out.println("Pruning: <" + low._nRefID + "," + low._dOffset + "," + low._dMult + ">");
						//System.out.println("Pruning: <" + high._nRefID + "," + high._dOffset + "," + high._dMult + ">");
						//System.out.println("Approximation error -> " + approx_err/range + " * " + range + " = " + approx_err);
						
						switch (PRUNE_TYPE) {
						case NO_REPLACE:
						case REPLACE_LOW:
						case REPLACE_HIGH: {
						}
							break;
						case REPLACE_MIN: {
							PRECISION_PRUNES++;
							retp = new PruneResult(new AADDRNode(low._nRefID, 
									Math.min(low._dOffset, high._dOffset), 
									Math.min(low._dMult, high._dMult)), ret._allow_err - approx_err);
						} break;
						case REPLACE_MAX: {
							PRECISION_PRUNES++;
							retp = new PruneResult(new AADDRNode(low._nRefID, 
									Math.max(low._dOffset, high._dOffset), 
									Math.max(low._dMult, high._dMult)), ret._allow_err - approx_err);
						} break;
						case REPLACE_AVG: {
							PRECISION_PRUNES++;
							// Error is 2* here b/c for a fun value, may go +approx_err/2 
							// on one side and -approx_err/2 on other
							retp = new PruneResult(new AADDRNode(low._nRefID, 
									(low._dOffset + high._dOffset)/2d, 
									(low._dMult + high._dMult)/2d), ret._allow_err - approx_err);
						} break;
						default: {
							System.out.println("Illegal replacement type " + PRUNE_TYPE);
							System.exit(1);
						} break;
						}
					}
					
					// **Must deal with numerical precision error**
					if ((retp != null) && (retp._rnode._nRefID != 0)
							&& (retp._rnode._dMult <= PRECISION)) {
						//System.out.println(ret.toString(this, 0));
						if (WARNING) {
							System.out.println("WARNING: Mult near 0 in getINode()");
						}
						//System.out.println("WARNING: Mult near 0 in getINode()");
						//System.exit(1);
						retp._allow_err -= range*retp._rnode._dMult;
						retp._rnode = new AADDRNode(0, retp._rnode._dOffset, 0d);
					}

					if (retp != null) {
						retp._rnode._dMult = r._dMult * retp._rnode._dMult;
						retp._rnode._dOffset = r._dMult * retp._rnode._dOffset + r._dOffset;
						//System.out.println("Pruning result: <" + retp._rnode._nRefID + "," + retp._rnode._dOffset + "," + retp._rnode._dMult + ">");
						_hmPruneMap.put(new ADDRNode(r._nRefID), retp._rnode);				
						return retp;
					}

			}
			
			AADDRNode low2 = new AADDRNode(low._nRefID, 0d, 1d);
			AADDRNode high2 = new AADDRNode(high._nRefID, 0d, 1d);

			// Now compute diff at this level
			AADDRNode adiff = applyInt(low2, high2, AADD.ARITH_MINUS);
			double max_abs_diff = Math.max(Math.abs(adiff._dOffset), Math
					.abs(adiff._dOffset + adiff._dMult)) / 2d;

			// DONE: Ensure range multiplication is correct... do range of
			//       low/high have to be multiplied into max_abs_diff above?
			//       low2 and high2 haven't taken these into account.
			//       --- I think OK, because INode is normalized to 1 so
			//           difference of functions is scaled by < 1,
			//           may be actually overconservative, but guarantees
			//           max of epsilon
			//
			//
			// DONE: Ensure that for re-pruning, the new error is modulated
			//       by the currently allowed error.
			//
			// DONE: Check the size of the sum diagram (and subtract diagram?)... 
			//       if larger, do not permit.
			//
			// TODO: Geometric approximation for product diagrams?

			// ///////////////// DEBUG ////////////////////
			//System.out.println("---------------------------------");
			//System.out.println("PRUNE = " + (/* check already linear! */ (low2._nRefID != high2._nRefID) 
			//		&& (PRUNE_PRECISION >= 0.0d) && ((range * max_abs_diff) <= PRUNE_PRECISION)));
			//System.out.println("Pruning type: " + PRUNE_TYPE + " @ node ID #" + r._nRefID);
			//System.out.println("Range: " + range + " * " + max_abs_diff + " = " + (range*max_abs_diff));
			//System.out.println("Pruning: \n" + r._nRefID);
			//System.out.println("Left:  \n" + low2.toString(this, 0));
			//System.out.println("Right: \n" + high2.toString(this, 0));
			// ////////////////////////////////////////////
			
			AADDRNode res = null;
			if (/* check already linear! */(low2._nRefID != high2._nRefID)
					&& ((range * max_abs_diff) <= ret._allow_err)) {

				switch (PRUNE_TYPE) {
				case NO_REPLACE: {
					ret._rnode = getINode(ni._nGlobalID, low._nRefID, high._nRefID,
							low._dOffset, low._dMult, high._dOffset,
							high._dMult, true);
				}
					break;
				case REPLACE_LOW: {
					ret._rnode = low;
				}
					break;
				case REPLACE_HIGH: {
					ret._rnode = high;
				}
					break;
				case REPLACE_MIN: {
					ret._rnode = applyInt(low, high, ARITH_MIN);
					ret._allow_err -= range * max_abs_diff;
				}
					break;
				case REPLACE_MAX: {
					ret._rnode = applyInt(low, high, ARITH_MAX);
					ret._allow_err -= range * max_abs_diff;
				}
					break;
				case REPLACE_AVG: {
					// Result must have range [0,1]
					//System.out.println("Replacing average:");
					res = scalarMultiply(applyInt(low2, high2, ARITH_SUM), 0.5d);
					long orig_size = countExactNodesFromINode(/*r._nRefID*/low2._nRefID) +
						countExactNodesFromINode(high2._nRefID);
					ret._rnode = getINode(ni._nGlobalID, res._nRefID, res._nRefID,
							low._dOffset, low._dMult, high._dOffset,
							high._dMult, true);
					long avg_size = countExactNodesFromINode(res._nRefID);
					//System.out.println("Old size: " + orig_size
					//		+ ", new size: " + avg_size);

					// Check that diagram did actually shrink
					if (avg_size <= orig_size) {
						// Now recursively re-prune with remaining precision
						ret._allow_err -= range * max_abs_diff;
						//System.out.println("- SECOND RECURSION " + r._nRefID + " with allowable error: " + ret._allow_err);
						ret = pruneNodeDiffOld(ret._rnode, range, true, ret._allow_err);
						
					} else {
						
						// TODO: Should be special case in Apply for sum of two linear functions
						//       to ensure no blowup and reduce numerical precision error.
						
						// Size blew up, do not prune!
						System.out.println("Node count before [" + orig_size
								+ "], after [" + avg_size + "], not pruned");
						
						System.out.println("SHOULD NOT HAPPEN");
						
						// No pruning, return original
						ret._rnode = getINode(ni._nGlobalID, low._nRefID, high._nRefID,
								low._dOffset, low._dMult, high._dOffset,
								high._dMult, true);

						/*
						
						//Graph g1 = getGraph(addRNodeRef(r));
						//g1.launchViewer(1300, 770);
						int low2_ref = addRNodeRef(low2);
						Graph gl = getGraph(low2_ref);
						gl.launchViewer(1300, 770);
						System.out.println(printNode(low2_ref) + "\n");
						
						int high2_ref = addRNodeRef(high2);
						Graph gh = getGraph(high2_ref);
						gh.launchViewer(1300, 770);
						System.out.println(printNode(high2_ref) + "\n");
						
						// TODO: Numerical precision error is creeping in here
						int sum_ref = addRNodeRef(applyInt(low2, high2, ARITH_SUM));
						//AADD.MERGE_IDENT_SUBNODES = true;
						int sum_reduce = reduce(sum_ref);
						Graph g2 = getGraph(sum_ref);
						g2.launchViewer(1300, 770);
						System.out.println(printNode(sum_ref) + "\n");
						System.out.println(printNode(sum_reduce) + "\n");

						ret._rnode = getINode(ni._nGlobalID, low._nRefID,
								high._nRefID, low._dOffset, low._dMult,
								high._dOffset, high._dMult, true);
						while (true);
						*/
					}
				}
					break;
				default: {
					System.out
							.println("Illegal replacement type " + PRUNE_TYPE);
					System.exit(1);
				}
				}

				// ////////////////////////////////////////////
				//System.out.println("= Sum: \n" + res.toString(this, 0));
				//System.out.println("=> Result: \n" + ret.toString(this, 0));
				//System.out.println("---------------------------------");
				// ////////////////////////////////////////////

				PRECISION_PRUNES++;

			} else {

				// Retrieve the inode
				ret._rnode = getINode(ni._nGlobalID, low._nRefID, high._nRefID,
						low._dOffset, low._dMult, high._dOffset, high._dMult,
						true);

			}

			// Cache the node in canonical form
			_hmPruneMap.put(new ADDRNode(r._nRefID), ret._rnode);

		} else {
			PRUNE_CACHE_HITS++;
		}

		//PRUNE_PRECISION += ;
		
		// Return cached value modified by offset
		ret._rnode = new AADDRNode(ret._rnode._nRefID, (r._dMult * ret._rnode._dOffset)
				+ r._dOffset, (r._dMult * ret._rnode._dMult));
		
		//System.out.println("EXITING " + r._nRefID + " with allowable error: " + ret._allow_err);
		
		return ret;
	}

	///////////////////////////////////////////////////////////////////////////
	//                             Main Algorithms
	///////////////////////////////////////////////////////////////////////////

	// Assume already built with correct order, just needs reduction
	public void reduce() {
		setRoot(reduceRestrict(_pRoot, this, -1, -1 /* Don't apply any op! */));
	}

	public int reduce(int root) {
		AADDRNode ret = reduceRestrict(getRNode(root), this, -1, -1);
		return addRNodeRef(ret);
	}

	// Assume already built with correct order, just needs reduction
	// This also performs restriction (use op = AADD.RESTRICT_LOW/HIGH).
	public void restrict(int gid, int op) {
		setRoot(reduceRestrict(_pRoot, this, gid, op));
	}

	public int restrict(int root, int gid, int op) {
		AADDRNode ret = reduceRestrict(getRNode(root), this, gid, op);
		return addRNodeRef(ret);
	}

	public AADDRNode reduceRemap(AADDRNode r, HashMap<Integer,Integer> remap) {
		// Can immediately check for local ID of 0
		if (r._nRefID == 0) {
			return r;
		}

		// Check cache
		AADDRNode ret = null;
		ReduceCacheKey key = new ReduceCacheKey(this, 0, 0, r._nRefID);

		if ((ret = (AADDRNode) _hmReduceRemap.get(key)) == null) {

			// Not in cache, perform reduction on this AADDINode
			boolean recurse = true;
			AADDINode ni = (AADDINode) getNode(r._nRefID);

			// Get high and low branches for this INode
			int nlow  = getRemappedNodeID(ni._nLow,  remap);
			int nhigh = getRemappedNodeID(ni._nHigh, remap);
			AADDRNode op1 = new AADDRNode(nlow, ni._dLowOffset,
					ni._dLowMult);
			AADDRNode op2 = new AADDRNode(nhigh, ni._dHighOffset,
					ni._dHighMult);

			// Get new low and high branches
			AADDRNode low = reduceRemap(op1, remap);
			AADDRNode high = reduceRemap(op2, remap);

			// Retrieve the inode
			ret = getINode(ni._nGlobalID, low._nRefID, high._nRefID,
					low._dOffset, low._dMult, high._dOffset, high._dMult,
					true);

			// Cache the node in canonical form
			_hmReduceRemap.put(key, ret);
		} else {
			REDUCE_CACHE_HITS++;
		}

		// Return cached value modified by offset
		return new AADDRNode(ret._nRefID, (r._dMult * ret._dOffset)
				+ r._dOffset, (r._dMult * ret._dMult));
	}

	
	// This is really a superset of reduce().  It only adds a check for
	// a gid and a restriction if that gid is found.  Otherwise,
	// everything is the same and the rest of the code is present
	// to perform an in-line reduction.
	//
	// In reality, a full AADD package only needs reduceRestrict(), opOut(),
	// Apply(), getINode(), computeTermNode(), and evaluate() for full
	// capability / efficiency.  Note that reduceRestrict(...,-1,-1) is
	// equivalent to reduce().
	//
	// If 'src' is non-null, this will obtain the node structure
	// from the ADD given by src.  In this case, the src
	// structure will remain unchanged.
	public AADDRNode reduceRestrict(AADDRNode r, AADD src, int gid, int op) {
		// Can immediately check for local ID of 0
		if (r._nRefID == 0) {
			return r;
		}

		// Check cache
		AADDRNode ret = null;
		ReduceCacheKey key = new ReduceCacheKey(src, gid, op, r._nRefID);

		if ((ret = (AADDRNode) _hmReduceMap.get(key)) == null) {

			// Not in cache, perform reduction on this AADDINode
			boolean recurse = true;
			AADDINode ni = (AADDINode) src.getNode(r._nRefID);

			// Op out, else reduce...
			if (ni._nGlobalID == gid) {

				// Get high and low branches 
				AADDRNode op1 = new AADDRNode(ni._nLow, ni._dLowOffset,
						ni._dLowMult);
				AADDRNode op2 = new AADDRNode(ni._nHigh, ni._dHighOffset,
						ni._dHighMult);

				// TODO: For restriction, it is inefficient and unnecessary
				//       to recurse.
				// Get application of op to low and high branches
				if (op == RESTRICT_HIGH || op == RESTRICT_LOW) {
					ret = ((op == RESTRICT_LOW) ? reduceRestrict(op1, src, gid,
							op) : reduceRestrict(op2, src, gid, op));
				} else {
					System.out.println("ERROR: op not a RESTRICT!");
					System.exit(1);
				}

			} else {

				// Get high and low branches for this INode
				AADDRNode op1 = new AADDRNode(ni._nLow, ni._dLowOffset,
						ni._dLowMult);
				AADDRNode op2 = new AADDRNode(ni._nHigh, ni._dHighOffset,
						ni._dHighMult);

				// Get new low and high branches
				AADDRNode low = reduceRestrict(op1, src, gid, op);
				AADDRNode high = reduceRestrict(op2, src, gid, op);

				// Retrieve the inode
				ret = getINode(ni._nGlobalID, low._nRefID, high._nRefID,
						low._dOffset, low._dMult, high._dOffset, high._dMult,
						true);
			}

			// Cache the node in canonical form
			_hmReduceMap.put(key, ret);
		} else {
			REDUCE_CACHE_HITS++;
		}

		// Return cached value modified by offset
		return new AADDRNode(ret._nRefID, (r._dMult * ret._dOffset)
				+ r._dOffset, (r._dMult * ret._dMult));
	}

	public int opOut(int root, int gid, int op) {
		AADDRNode ret = opOut(getRNode(root), gid, op);
		return addRNodeRef(ret);
	}

	// For marginalizing out a node via sum, prod, max, or min.
	public AADDRNode opOut(AADDRNode r, int gid, int op) {

		// Check for valid operator
		if (op != ARITH_SUM && op != ARITH_PROD && op != ARITH_MAX
				&& op != ARITH_MIN) {
			System.out.println("ERROR: opOut called without SUM/PROD/MIN/MAX");
			System.exit(1);
		}

		// Need left and right operands... can do a quick shortcut if top node
		// has global var, i.e., just take left and right branch and perform op.
		AADDRNode high_br = null, low_br = null;
		AADDINode ni = null;
		if (r._nRefID != 0
				&& ((ni = (AADDINode) getNode(r._nRefID))._nGlobalID == gid)
				&& op == ARITH_SUM) {

			// Get high and low branches for this INode
			high_br = new AADDRNode(ni._nHigh, ni._dHighOffset, ni._dHighMult);
			low_br = new AADDRNode(ni._nLow, ni._dLowOffset, ni._dLowMult);
			AADDRNode ret = applyInt(high_br, low_br, op);
			return new AADDRNode(ret._nRefID, (r._dMult * ret._dOffset) + 2d
					* r._dOffset, (r._dMult * ret._dMult));

		} else {

			// Get high and low branch restrictions for this var
			high_br = reduceRestrict(r, this, gid, RESTRICT_HIGH);
			low_br = reduceRestrict(r, this, gid, RESTRICT_LOW);
			return applyInt(high_br, low_br, op);
		}
	}

	public int remapGIDsInt(int rid, HashMap gid_map) {
		AADDRNode r = getRNode(rid);
		AADDRNode ret = new AADDRNode(remapGIDs(r._nRefID, gid_map),
				r._dOffset, r._dMult);
		return addRNodeRef(ret);
	}

	// Remap gids in internal nodes - map is old_id -> new_id.
	// TODO: Assuming consistent order but not checking!!!
	public void remapGIDs(HashMap gid_map) {
		setRoot(new AADDRNode(remapGIDsInt(_pRoot._nRefID, gid_map),
				_pRoot._dOffset, _pRoot._dMult));
	}

	public int remapGIDs(int local_id, HashMap gid_map) {
		if (local_id == 0) {
			return 0;
		} else { // n instanceof ADDINode so recurse and update caches
			AADDINode ni = (AADDINode) getNode(local_id);
			Integer old_id = new Integer(ni._nGlobalID);
			Integer new_id = (Integer) gid_map.get(old_id);
			if (new_id == null) {
				new_id = old_id;
			}
			return getINode(new_id.intValue(), remapGIDs(ni._nLow, gid_map),
					remapGIDs(ni._nHigh, gid_map), ni._dLowOffset,
					ni._dLowMult, ni._dHighOffset, ni._dHighMult, true)._nRefID;
		}
	}

	public boolean verifyOrder(int id) {
		return verifyOrder(getRNode(id)._nRefID, -1);
	}

	// A quick test to verify canonical order!  Returns false if problem.
	public boolean verifyOrder() {
		return verifyOrder(_pRoot._nRefID, -1);
	}

	public boolean verifyOrder(int n, int par_gid) {
		if (n != 0) {
			AADDINode ni = (AADDINode) getNode(n);
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

	// Assume a1 and a2 are ordered, op is +,*,max.
	// Uses root of each AADD and builds a new AADD to return.
	public static AADD Apply(AADD a1, AADD a2, int op) {
		// Check for invalid restrict operation
		if (op == AADD.RESTRICT_LOW || op == AADD.RESTRICT_HIGH) {
			System.out.println("Cannot RESTRICT using Apply(...)");
			System.exit(1);
		}

		AADD result = new AADD(a1._alOrder);
		// result._nWhich = (a1._nWhich != 0) ? a1._nWhich : a2._nWhich;

		// Now that order is correct, apply op
		result.setRoot(result.apply(a1._pRoot, a1, a2._pRoot, a2, op));

		return result;
	}

	// Nodes can be external to this, will be internalized.  Result will be within "this".
	public AADDRNode apply(AADDRNode a1, AADD ctxt1, AADDRNode a2, AADD ctxt2,
			int op) {
		//Compare.ResetTimer();
		if (ctxt1 != this) {
			a1 = reduceRestrict(a1, ctxt1, -1, -1);
		}

		if (ctxt2 != this) {
			a2 = reduceRestrict(a2, ctxt2, -1, -1);
		}

		//System.out.print(" *" + Compare.GetElapsedTime() + "* ");
		//Compare.ResetTimer();
		return applyInt(a1, a2, op);
	}

	// The 'int' internal interface to apply
	public int applyInt(int a1, int a2, int op) {
		AADDRNode r1 = getRNode(a1);
		AADDRNode r2 = getRNode(a2);
		AADDRNode ret = applyInt(r1, r2, op);
		return addRNodeRef(ret);
	}

	// Nodes must be internal!
	public AADDRNode applyInt(AADDRNode a1, AADDRNode a2, int op) {
		///////////////////////////////////////////////////////////////////////////
		// Debug printing
		int min_gid = 1000000;
		if (PRINT_DEBUG && PRINT_APPLY) {
			ADDNode nt1 = getNode(a1._nRefID);
			ADDNode nt2 = getNode(a2._nRefID);
			if (nt1 instanceof AADDINode) {
				min_gid = ((AADDINode) nt1)._nGlobalID;
			}
			if (nt2 instanceof AADDINode) {
				min_gid = Math.min(min_gid, ((AADDINode) nt2)._nGlobalID);
			}
			if (min_gid == 1000000) {
				System.out.print(ADDNode.indent(((Integer) _alOrder
						.get(_alOrder.size() - 1)).intValue() - 1));
			} else {
				System.out.print(ADDNode.indent(min_gid - 2));
			}
			System.out.println(((min_gid == 1000000) ? 0 : min_gid)
					+ ": Apply: [a1: " + "<" + _df.format(a1._dOffset) + ", "
					+ _df.format(a1._dMult) + ", " + a1._nRefID + ">" + ";  a2: "
					+ "<" + _df.format(a2._dOffset) + ", " + _df.format(a2._dMult)
					+ ", " + a2._nRefID + ">" + ";  op: " + op + "]");
		}
		///////////////////////////////////////////////////////////////////////////

		// Can we compute a result immediately?
		AADDRNode ret = null;
		if ((ret = computeTermNode(a1, a2, op)) != null) {

			// We will not cache term node computations (since they are either
			// simple or subprocedures will cache the results).  So just return
			// value here.
			//if (PRINTING_ON)
			//	System.out.println("ComputeTermNode found a result.");
			return ret;
		}

		// Get the normalized cache key
		boolean min_max_cache = false;
		SAINodeIndex key = null;
		if ((op == ARITH_SUM) || (op == ARITH_MINUS && a1._dMult != 0)) {
			key = new SAINodeIndex(op, a1._nRefID, a2._nRefID, 0d, 1d, 0d,
					a2._dMult / a1._dMult);
		} else if (op == ARITH_PROD) {
			key = new SAINodeIndex(op, a1._nRefID, a2._nRefID, a1._dOffset
					/ a1._dMult, 1d, a2._dOffset / a2._dMult, 1d);
		} else if (((op == ARITH_MIN) || (op == ARITH_MAX)) && a1._nRefID != 0
				&& a2._nRefID != 0) {
			min_max_cache = true;
			key = new SAINodeIndex(op, a1._nRefID, a2._nRefID, 0d, 1d,
					(a2._dOffset - a1._dOffset) / a1._dMult, a2._dMult
							/ a1._dMult);
		} else {
			key = new SAINodeIndex(op, a1._nRefID, a2._nRefID, a1._dOffset,
					a1._dMult, a2._dOffset, a2._dMult);
		}

		// Check cache
		if ((ret = (AADDRNode) _hmApplyCache.get(key)) != null) {

			// Just keep track of cache statistics
			switch (op) {
			case ARITH_SUM:
			case ARITH_MINUS:
				SUM_CACHE_HITS++;
				break;
			case ARITH_PROD:
				PROD_CACHE_HITS++;
				break;
			case ARITH_MAX:
			case ARITH_MIN:
				MAX_CACHE_HITS++;
				break;
			default:
				APPLY_CACHE_HITS++;
				break;
			}

		} else { // ret is null, must recurse

			// Not in cache and at least one node must be internal.
			int rvar, id_v1_low, id_v1_high;
			int id_v2_low, id_v2_high;
			double o_v1_low, m_v1_low;
			double o_v1_high, m_v1_high;
			double o_v2_low, m_v2_low;
			double o_v2_high, m_v2_high;

			// Retrieve nodes 
			ADDNode n1 = getNode(a1._nRefID);
			ADDNode n2 = getNode(a2._nRefID);

			// Find node with min id (or only internal node)
			if (n1 instanceof AADDINode) {
				if (n2 instanceof AADDINode) {
					if (comesBefore(((AADDINode) n1)._nGlobalID,
							((AADDINode) n2)._nGlobalID)) {
						rvar = ((AADDINode) n1)._nGlobalID;
					} else {
						rvar = ((AADDINode) n2)._nGlobalID;
					}
				} else {
					rvar = ((AADDINode) n1)._nGlobalID;
				}
			} else {
				rvar = ((AADDINode) n2)._nGlobalID;
			}

			// Determine next recursion for n1
			if ((n1 instanceof AADDINode)
					&& (((AADDINode) n1)._nGlobalID == rvar)) {
				id_v1_low = ((AADDINode) n1)._nLow;
				id_v1_high = ((AADDINode) n1)._nHigh;
				o_v1_low = key._dOffset1 + key._dMult1
						* ((AADDINode) n1)._dLowOffset;
				o_v1_high = key._dOffset1 + key._dMult1
						* ((AADDINode) n1)._dHighOffset;
				m_v1_low = key._dMult1 * ((AADDINode) n1)._dLowMult;
				m_v1_high = key._dMult1 * ((AADDINode) n1)._dHighMult;
			} else {
				id_v1_low = id_v1_high = a1._nRefID;
				o_v1_low = o_v1_high = key._dOffset1;
				m_v1_low = m_v1_high = key._dMult1;
			}

			// Determine next recursion for n2
			if ((n2 instanceof AADDINode)
					&& (((AADDINode) n2)._nGlobalID == rvar)) {
				id_v2_low = ((AADDINode) n2)._nLow;
				id_v2_high = ((AADDINode) n2)._nHigh;
				o_v2_low = key._dOffset2 + key._dMult2
						* ((AADDINode) n2)._dLowOffset;
				o_v2_high = key._dOffset2 + key._dMult2
						* ((AADDINode) n2)._dHighOffset;
				m_v2_low = key._dMult2 * ((AADDINode) n2)._dLowMult;
				m_v2_high = key._dMult2 * ((AADDINode) n2)._dHighMult;
			} else {
				id_v2_low = id_v2_high = a2._nRefID;
				o_v2_low = o_v2_high = key._dOffset2;
				m_v2_low = m_v2_high = key._dMult2;
			}

			// Now compute the appropriate branches
			AADDRNode low = applyInt(new AADDRNode(id_v1_low, o_v1_low,
					m_v1_low), new AADDRNode(id_v2_low, o_v2_low, m_v2_low), op);

			AADDRNode high = applyInt(new AADDRNode(id_v1_high, o_v1_high,
					m_v1_high),
					new AADDRNode(id_v2_high, o_v2_high, m_v2_high), op);

			// Retrieve the AADDINode (getINode will take care of 'low==high')
			ret = getINode(rvar, low._nRefID, high._nRefID, low._dOffset,
					low._dMult, high._dOffset, high._dMult, true);

			// Cache result for previously determined key
			_hmApplyCache.put(key, ret);
		}

		// Now, modify the node as required to obtain the actual result
		if ((op == ARITH_SUM) || (op == ARITH_MINUS && a1._dMult != 0)) {
			ret = new AADDRNode(ret._nRefID, (a1._dMult * ret._dOffset)
					+ a1._dOffset
					+ ((op == ARITH_SUM) ? a2._dOffset : -a2._dOffset),
					a1._dMult * ret._dMult);
		} else if (op == ARITH_PROD) {
			ret = scalarMultiply(ret, a1._dMult * a2._dMult);
		} else if (min_max_cache) {
			ret = new AADDRNode(ret._nRefID, (a1._dMult * ret._dOffset)
					+ a1._dOffset, a1._dMult * ret._dMult);
		}

		///////////////////////////////////////////////////////////////////////////
		// Debug printing
		if (PRINT_DEBUG && PRINT_APPLY) {
			if (min_gid == 1000000) {
				System.out.print(ADDNode.indent(((Integer) _alOrder
						.get(_alOrder.size() - 1)).intValue() - 1));
			} else {
				System.out.print(ADDNode.indent(min_gid - 2));
			}
			System.out.println("-->" + ((min_gid == 1000000) ? 0 : min_gid)
					+ ": " + "<" + _df.format(ret._dOffset) + ", "
					+ _df.format(ret._dMult) + ", " + ret._nRefID + ">");
		}
		///////////////////////////////////////////////////////////////////////////

		// Return result of apply
		return ret;
	}
	
	// Computes a terminal node value if possible.  Can short circuit
	// the computation in many cases!
	public AADDRNode computeTermNode(AADDRNode a1, AADDRNode a2, int op) {

		AADDRNode ret = null;

		if (a1._nRefID == 0 && a2._nRefID == 0) {

			// Can we create a terminal node here?
			switch (op) {
			case ARITH_SUM: {
				ret = new AADDRNode(0, a1._dOffset + a2._dOffset, 0);
			}
				break;
			case ARITH_PROD: {
				//if (PRINTING_ON) System.out.println("CTerm 0: " + a1._dOffset + 
				//		", " + a2._dOffset + " = " + (a1._dOffset * a2._dOffset));
				ret = new AADDRNode(0, a1._dOffset * a2._dOffset, 0);
			}
				break;
			case ARITH_MAX: {
				ret = new AADDRNode(0, Math.max(a1._dOffset, a2._dOffset), 0);
			}
				break;
			case ARITH_MIN: {
				ret = new AADDRNode(0, Math.min(a1._dOffset, a2._dOffset), 0);
			}
				break;
			case ARITH_DIV: {
				ret = new AADDRNode(0, a1._dOffset / a2._dOffset, 0);
				if (ret._dOffset == Double.POSITIVE_INFINITY
						|| ret._dOffset == Double.NEGATIVE_INFINITY) {
					System.out.println("\n**ERROR**: Divide by ZERO");
				}
			}
				break;
			case ARITH_MINUS: {
				ret = new AADDRNode(0, a1._dOffset - a2._dOffset, 0);
			}
				break;
			default: {
				System.out.println("Unknown operation: " + op);
				System.exit(1);
			}
			}

		} else if (op == ARITH_MIN || op == ARITH_MAX) {

			if (op == ARITH_MIN) {

				if ((a1._dOffset + a1._dMult) <= a2._dOffset) {
					// max of a1 is less than min of a2
					ret = a1;
					MIN_PRUNE_CNT++;
				} else if ((a2._dOffset + a2._dMult) <= a1._dOffset) {
					// max of a2 is less than min of a1
					ret = a2;
					MIN_PRUNE_CNT++;
				}

			} else if (op == ARITH_MAX) {

				if ((a1._dOffset + a1._dMult) <= a2._dOffset) {
					// max of a1 is less than min of a2
					ret = a2;
					MAX_PRUNE_CNT++;
				} else if ((a2._dOffset + a2._dMult) <= a1._dOffset) {
					// max of a2 is less than min of a1
					ret = a1;
					MAX_PRUNE_CNT++;
				}

			}

		} else {

			AADDRNode tnode = null;
			AADDRNode other = null;

			if (a1._nRefID == 0) {
				tnode = a1;
				other = a2;
			} else if (a2._nRefID == 0) {
				tnode = a2;
				other = a1;
			}

			if (tnode != null) {

				// tnode is a terminal node, other is not!
				// Can do DIV and MINUS here if keep track of order...
				switch (op) {
				case ARITH_SUM: {
					ret = new AADDRNode(other._nRefID, tnode._dOffset
							+ other._dOffset, other._dMult);

					TERM_PRUNE_CNT++;
				}
					break;
				case ARITH_PROD: {
					// RANGE_SCALE only
					// Need to multiply other node by tnode._dOffset...
					// can only do this if we're normalizing, otherwise
					// cannot have non-1d multiplier.
					if (tnode._dOffset < 0d) {
						other = applyInt(getDNode(0d, true), other, ARITH_MINUS);
						ret = scalarMultiply(other, -tnode._dOffset);
					} else {
						ret = scalarMultiply(other, tnode._dOffset);
					}
						
					PROD_PRUNE_CNT++;
					TERM_PRUNE_CNT++;
					//if (PRINTING_ON) System.out.println("CTerm 1");
				}
					break;
				case ARITH_MIN:
				case ARITH_MAX: {
					System.out
							.println("computeTermNode(): Should not get here!");
					System.exit(1);
				}
					break;

				case ARITH_MINUS: {
					if (tnode == a2) {
						ret = new AADDRNode(other._nRefID, other._dOffset
								- tnode._dOffset, other._dMult);
					}
					TERM_PRUNE_CNT++;
				}
					break;
				}

			}
		}

		// If still no result, test to see if identical pruning
		if (ret == null
				&& (a1._nRefID == a2._nRefID)
				&& (op == ARITH_SUM || op == ARITH_PROD || op == ARITH_MAX || op == ARITH_MIN)) { //|| op == ARITH_MINUS

			// Here we can be efficient due to the subnodes being identical
			switch (op) {

			case ARITH_SUM: {

				// Can always prune
				//System.out.println("Prune ident sum " + a1._nRefID + ", "
				//		+ a2._nRefID); // REMOVE
				ret = new AADDRNode(a1._nRefID, a1._dOffset + a2._dOffset,
						a1._dMult + a2._dMult);

			}
				break;

			case ARITH_MAX: {

				// Now determine if we can prune
				//System.out.println("Prune ident max " + key1 + ", " + key2); // REMOVE
				if (a1._dOffset >= a2._dOffset && a1._dMult >= a2._dMult) {
					ret = a1;
				} else if (a2._dOffset >= a1._dOffset && a2._dMult >= a1._dMult) {
					ret = a2;
				}

			}
				break;

			case ARITH_MIN: {

				// Now determine if we can prune
				if (a1._dOffset <= a2._dOffset && a1._dMult <= a2._dMult) {
					ret = a1;
				} else if (a2._dOffset <= a1._dOffset && a2._dMult <= a1._dMult) {
					ret = a2;
				}

			}
				break;

			}

			if (ret != null) {
				IDENT_PRUNES++;
			}

		}

		return ret;
	}

	public double evaluate(int rid, ArrayList assign) {
		return evaluate(getRNode(rid), assign);
	}

	// Takes an assignment of gvars->{T|F} (Boolean class) and returns
	// the corresponding terminal node.  
	public double evaluate(AADDRNode r, ArrayList assign) {

		Boolean b;
		double offset = r._dOffset;
		double mult = r._dMult;
		ADDNode cur = getNode(r._nRefID);

		while (cur instanceof AADDINode) {
			AADDINode curi = (AADDINode) cur;
			int level = ((Integer) _hmGVarToLevel.get(new Integer(
					((AADDINode) cur)._nGlobalID))).intValue();

			// If we need a var that is unassigned, return null
			// System.out.print("<" + _df.format(offset) + ", " + _df.format(mult) + "> ");
			if ((level < assign.size())
					&& ((b = (Boolean) assign.get(level)) != null)) {
				cur = (b.booleanValue()) ? getNode(curi._nHigh)
						: getNode(curi._nLow);
				offset += mult
						* ((b.booleanValue()) ? curi._dHighOffset
								: curi._dLowOffset);
				mult *= (b.booleanValue()) ? curi._dHighMult : curi._dLowMult;
			} else {
				return Double.NaN;
			}
		}

		// If get here, cur will be an AADDINode, ADDDNode
		return offset;
	}

	/////////////////////////////////////////////////////////////////
	//                       Order maintenance
	/////////////////////////////////////////////////////////////////

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

	////////////////////////////////////////////////////////////////
	//              Construction and File I/O Routines
	////////////////////////////////////////////////////////////////

	// Note: Following functions are identical to ADD counterparts
	// These are inefficient because they rely on the 'int'
	// interface... could update for AADDRNode interface eventually.

	/** Build an ADD from a list (node is a list, high comes first
	 ** for internal nodes)
	 **/
	public int buildDDFromUnorderedTree(ArrayList l, Map var2ID) {
		AADDRNode ret = buildDDFromUnorderedTreeInt(l, var2ID);
		int rnode_ref = addRNodeRef(ret);
		return rnode_ref;
	}

	//public static boolean PRINTING_ON = false;
	public AADDRNode buildDDFromUnorderedTreeInt(ArrayList l, Map var2ID) {
		Object o = l.get(0);
		if (o instanceof String && HasOnlyDigits((String) o)) {
			double val = (new BigInteger((String) o)).doubleValue();
			return getDNode(val, true);
		} else if (o instanceof BigDecimal) {
			double val = ((BigDecimal) o).doubleValue();
			boolean neg = val < 0;
			if (neg)
				val = -val;
			AADDRNode dnode = getDNode(val, true);
			if (neg) {
				AADDRNode zero = getDNode(0d, true);
				dnode = applyInt(zero, dnode, ARITH_MINUS);
			}
			//if (PRINTING_ON)
			//	System.out.println("AADD BigDecimal: " + printNode(addRNodeRef(dnode)));
			return dnode;
		} else {
			String var = (String) o;
			int gid = ((Integer) var2ID.get(var)).intValue();

			// Get the var ADD
			AADDRNode high_br = getVarNodeInt(gid, 0.0d, 1.0d);
			//if (PRINTING_ON)
			//	System.out.println("AADD Build 1: " + printNode(addRNodeRef(high_br)));
			high_br = applyInt(high_br, buildDDFromUnorderedTreeInt(
					(ArrayList) l.get(1), var2ID) /*high*/, ARITH_PROD);
			//if (PRINTING_ON)
			//	System.out.println("AADD Build 2: " + printNode(addRNodeRef(high_br)));

			// Get the !var ADD
			AADDRNode low_br = getVarNodeInt(gid, 1.0d, 0.0d);
			//if (PRINTING_ON)
			//	System.out.println("AADD Build 3: " + printNode(addRNodeRef(low_br)));
			low_br = applyInt(low_br, buildDDFromUnorderedTreeInt((ArrayList) l
					.get(2), var2ID) /*low*/, ARITH_PROD);
			//if (PRINTING_ON)
			//	System.out.println("AADD Build 4: " + printNode(addRNodeRef(low_br)));

			AADDRNode apply_result = applyInt(low_br, high_br, ARITH_SUM);
			//if (PRINTING_ON)
			//	System.out.println("AADD Build 5: " + printNode(addRNodeRef(apply_result)));
			return apply_result;
		}
	}

	/** Build an ADD from a list with correct variable order
	 ** (node is a list, high comes first for internal nodes)
	 **/
	public int buildDDFromOrderedTree(ArrayList l, Map var2ID) {
		AADDRNode ret = buildDDFromOrderedTreeInt(l, var2ID);
		return addRNodeRef(ret);
	}

	public AADDRNode buildDDFromOrderedTreeInt(ArrayList l, Map var2ID) {
		return reduceRestrict(buildNode(l, var2ID), this, -1, -1);
	}

	public AADDRNode buildNode(ArrayList l, Map var2ID) {

		Object o = l.get(0);
		if (o instanceof String && HasOnlyDigits((String) o)) {
			double v = (new BigInteger((String) o)).doubleValue();
			return getDNode(v, true);
		} else if (o instanceof BigDecimal) {
			double v = ((BigDecimal) o).doubleValue();
			return getDNode(v, true);
		} else {
			String var = (String) o;
			int gid = ((Integer) var2ID.get(var)).intValue();

			// Get the var AADD
			AADDRNode high = buildNode((ArrayList) l.get(1), var2ID);
			AADDRNode low = buildNode((ArrayList) l.get(2), var2ID);

			// Return the RNode ref to the normalized INode
			return getINode(gid, low._nRefID, high._nRefID, low._dOffset,
					low._dMult, high._dOffset, high._dMult, true);
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

	/** Build a constant ADD **/
	public static AADD GetConstantAADD(double val, ArrayList order) {
		AADD a = new AADD(order);
		AADDRNode n = a.getDNode(val, true);
		a.setRoot(n);

		return a;
	}

	/** Build a var ADD **/
	public static AADD GetVarAADD(int gid, double low, double high,
			ArrayList order) {

		if (order == null) {
			order = new ArrayList();
			order.add(new Integer(gid));
		}

		AADD a = new AADD(order);
		AADDRNode n = a.getINode(gid, 0, 0, low, 0.0d, high, 0.0d, true);
		a.setRoot(n);

		return a;
	}

	/** Build a var AADD **/
	public int getVarNode(int gid, double low, double high) {
		AADDRNode ret = getINode(gid, 0, 0, low, 0d, high, 0d, true);
		return addRNodeRef(ret);
	}

	/** Build a constant ADD */
	public int getConstantNode(double val) {
		AADDRNode ret = getDNode(val, true);
		return addRNodeRef(ret);
	}

	/** Build a var AADD **/
	public AADDRNode getVarNodeInt(int gid, double low, double high) {
		return getINode(gid, 0, 0, low, 0d, high, 0d, true);
	}

	/** Build a constant ADD */
	public AADDRNode getConstantNodeInt(double val) {
		return getDNode(val, true);
	}

	////////////////////////////////////////////////////////////////
	//                    Miscellaneous methods
	////////////////////////////////////////////////////////////////

	// Helper fun for formatting value range
	public ArrayList procList(ArrayList a) {
		ArrayList ret = new ArrayList();
		Iterator i = a.iterator();
		while (i.hasNext()) {
			ret.add(_df.format(((Double) i.next()).doubleValue()));
		}
		return ret;
	}

	public Object clone() {
		return new AADD(this);
	}

	public String toString() {

		StringBuffer sb = new StringBuffer();

		// Show order
		sb.append("Var order:  " + _alOrder + "\n");
		sb.append("GVar level: " + _hmGVarToLevel + "\n");
		// sb.append("Val range: " + procList(getValueRange()) + "\n");

		// Recurse from the root and show each branch
		sb.append("Structure:\n[ <" + _df.format(_pRoot._dOffset) + ","
				+ _df.format(_pRoot._dMult) + "> "
				+ getNode(_pRoot._nRefID).toString(this, 0) + "]\n");

		return sb.toString();
	}

	public String printNode(int rid) {
		return getRNode(rid).toString(this, 0);
	}

	public Graph getGraph(int id) {
		return getGraph(id, null);
	}

	public Graph getGraph(int rid, Map id2var) {
		Graph g = new Graph(true /* directed */, false /* bottom-to-top */,
	            /*left-to-right*/ false, true /* multi-links */);
		getRNode(rid).toGraph(this, g);
		if (id2var != null)
			g.remap(id2var);
		return g;
	}

	public void pruneReport() {
		System.out.println("Prune Report:\n-------------");
		System.out.println("TERM: " + TERM_PRUNE_CNT++);
		System.out.println("PROD: " + PROD_PRUNE_CNT++);
		System.out.println("MIN:  " + MIN_PRUNE_CNT++);
		System.out.println("MAX:  " + MAX_PRUNE_CNT++ + "\n");
		System.out.println("IDENT PRUNES:      " + IDENT_PRUNES++);
		System.out.println("PRECISION PRUNES:  " + PRECISION_PRUNES++);
		System.out.println("REDUCE CACHE HITS: " + REDUCE_CACHE_HITS++);
		System.out.println("APPLY CACHE HITS:  " + APPLY_CACHE_HITS++ + "\n");
		System.out.println("PRUNE CACHE HITS:  " + PRUNE_CACHE_HITS++);
		System.out.println("SUM CACHE HITS:    " + SUM_CACHE_HITS++);
		System.out.println("PROD CACHE HITS:   " + PROD_CACHE_HITS++);
		System.out.println("MAX CACHE HITS:    " + MAX_CACHE_HITS++);
	}

	// Helper class for comparing IDs
	public static class IDComparator implements Comparator {

		// For comparing two objects
		public int compare(Object o1, Object o2) {
			return ((Integer) o1).compareTo((Integer) o2);
		}

		// For comparing Comparators (never really used!)
		public boolean equals(Object obj) {
			return this == obj;
		}
	}
}
