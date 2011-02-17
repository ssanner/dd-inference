//////////////////////////////////////////////////////////////////////
//
// Algebraic Decision Diagram Package (Generic function bool ->real interface)
//
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
// Notes:
// ------
// - Nodes can either be Integer or Pair (if maintaining ranges).
//   Pair not implemented yet.
//
// TODO:
// -----
// - The reason for this class structure is that I want to implement
//   Pair which maintains a pair of DDs (one max, and one min) without
//   modifying the base decision diagram package... the only way to
//   do this is to encapsulate the DDs. 
//
// - Need to reintroduce Pair and range approximation capability.
//   How to keep track of which nodes for high and low ranges.
//   Occasionally things like normalization in Bayes nets need this
//   information (b/c division of max has to use min counterpart).
//
//////////////////////////////////////////////////////////////////////

package logic.add;

import java.math.*;
import java.text.*;
import java.util.*;

import graph.Graph;

public class FBR {

    // The context in which to do all DD manipulations
    public DD _context;

    // Initializes the global ADD/AADD to be used for all computations
    public FBR(int type, ArrayList order) {
	switch (type) {
	case DD.TYPE_TABLE: {
	    _context = new Table(order);
	} break;
	case DD.TYPE_ADD: {
	    _context = new ADD(order);
	} break;
	case DD.TYPE_AADD: {
	    _context = new AADD(order);
	} break;
	case DD.TYPE_LAADD: {
	    _context = new LAADD(order);
	} break;
	default: {
	    System.out.println("FBR.Initialize: Illegal TYPE");
	    System.exit(1);
	    _context = null;
	}
	}
    }

    // This is global for all DDs (currently), could make member var.
    // Also previously had DD._bPruneDuringApply... still need?
    public static void SetPruneInfo(int prune_type, double prune_prec) {
	DD.PRUNE_TYPE      = prune_type;
	DD.PRUNE_PRECISION = prune_prec;
    }
    
    /////////////////////////////////////////////////////////////////////////////
    //                      Generic Decision Diagram Operations
    /////////////////////////////////////////////////////////////////////////////

    // Designate/remove/clear nodes to persist through flushing
    public void addSpecialNode(Object id) {

    if (id == null)
    	return;
    	
	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    _context.addSpecialNode(i.intValue());

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    _context.addSpecialNode(p._o1.intValue());
	    _context.addSpecialNode(p._o2.intValue());
	}
    }

    public void removeSpecialNode(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    _context.removeSpecialNode(i.intValue());

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    _context.removeSpecialNode(p._o1.intValue());
	    _context.removeSpecialNode(p._o2.intValue());
	}
    }

    public void clearSpecialNodes() {

	_context.clearSpecialNodes();
    }

    // Flush caches but save special nodes.  
    public void flushCaches(boolean print_info) {

	_context.flushCaches(print_info);
    }

    //////////////////////////////////////////////////////////////////
    //                         Construction
    //////////////////////////////////////////////////////////////////

    // Build a var ADD 
    public Object getVarNode(int gid, double low, double high) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    return new Integer(_context.getVarNode(gid, low, high));

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }

    // Build a constant ADD
    public Object getConstantNode(double val) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    return new Integer(_context.getConstantNode(val));

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }

    // Build an ADD from a list (node is a list, high comes first for
    // internal nodes)
    public Object buildDDFromUnorderedTree(ArrayList l, Map var2ID) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    return new Integer(_context.buildDDFromUnorderedTree(l, var2ID));

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }
    
    // Build an ADD from a list with correct variable order (node is a
    // list, high comes first for internal nodes)
    public Object buildDDFromOrderedTree(ArrayList l, Map var2ID) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    return new Integer(_context.buildDDFromOrderedTree(l, var2ID));

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }

    //////////////////////////////////////////////////////////////////
    //           Construction / Application / Evaluation
    //////////////////////////////////////////////////////////////////

    // Internal and external Apply
    public Object applyInt(Object a1, Object a2, int op) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i1 = (Integer)a1;
	    Integer i2 = (Integer)a2;
	    return new Integer(_context.applyInt(i1.intValue(), i2.intValue(), op));

	} else {
	    // Handle Pair
	    Pair p1 = (Pair)a1;
	    Pair p2 = (Pair)a2;
	    return null; // TODO
	}

    }

    // For marginalizing out a node via sum, prod, max, or min.
    public Object opOut(Object id, int gid, int op) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return new Integer(_context.opOut(i.intValue(), gid, op));

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null; // TODO
	}

    }

    // For restricting a variable
    public Object restrict(Object id, int gid, int op) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return new Integer(_context.restrict(i.intValue(), gid, op));

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null; // TODO
	}

    }

    // Evaluate a DD: gid == val[assign_index] -> true/false
    public double evaluate(Object id, ArrayList assign) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.evaluate(i.intValue(), assign);

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return Double.NaN; // TODO
	}

    }

    // Remap gids... gid_map = old_id -> new_id (assuming order consistent)
    public Object remapGIDsInt(Object id, HashMap gid_map) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return new Integer(_context.remapGIDsInt(i.intValue(), gid_map));

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null; // TODO
	}

    }

    //////////////////////////////////////////////////////////////////
    //                    Arithmetic Operations
    //////////////////////////////////////////////////////////////////

    public double getMinValue(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.getMinValue(i.intValue());

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return Double.NaN; // TODO
	}

    }

    public double getMaxValue(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.getMaxValue(i.intValue());

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return Double.NaN; // TODO
	}

    }

    public Object scalarMultiply(Object id, double val) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Object
	    Integer i = (Integer)id;
	    return new Integer(_context.scalarMultiply(i.intValue(), val));	    

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }

    public Object scalarAdd(Object id, double val) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return new Integer(_context.scalarAdd(i.intValue(), val));	    

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null; // TODO
	}

    }

    // -DD
    public Object invert(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return new Integer(_context.invert(i.intValue()));	    

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null; // TODO
	}

    } 

    // 1/DD
    public Object negate(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return new Integer(_context.negate(i.intValue()));	    

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null; // TODO
	}

    } 

    //////////////////////////////////////////////////////////////////
    //                     Internal Statistics
    //////////////////////////////////////////////////////////////////

    // Quick cache snapshot
    public void showCacheSize() {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    _context.showCacheSize();

	} else {
	    // Handle Pair
	    System.out.println("FBR.showCacheSize() not implemented");
	}

    }

    // Total cache snapshot
    public long getCacheSize() {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    return _context.getCacheSize();

	} else {
	    // Handle Pair
	    return -1; // TODO
	}

    }

    // An exact count for the ADD rooted at _nRoot
    public long countExactNodes(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.countExactNodes(i.intValue());

	} else {
	    // Handle Pair
	    return -1; // TODO
	}

    }

    // Set of the actual node ids
    public Set getExactNodes(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.getExactNodes(i.intValue());

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }

    // Set of the actual variable ids
    public Set getGIDs(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.getGIDs(i.intValue());

	} else {
	    // Handle Pair
	    return null; // TODO
	}

    }

    //////////////////////////////////////////////////////////////////
    //                   Printing and Comparison
    //////////////////////////////////////////////////////////////////

    // Show pruning information
    public void pruneReport() {
	_context.pruneReport();
    }

    // Print out a node
    public String printNode(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    return _context.printNode(i.intValue());

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    return null;
	}
    }

    public Graph getGraph(Object id) {
    	return getGraph(id, null);
    }
    
   	public Graph getGraph(Object id, Map id2var) {

    	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
    	    // Handle Integer
    	    Integer i = (Integer)id;
    	    return _context.getGraph(i.intValue(), id2var);

    	} else {
    	    // Handle Pair
    	    Pair p = (Pair)id;
    	    return null;
    	}  	
    }
    
    // Printing out the full table
    public void printEnum(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i = (Integer)id;
	    DD.PrintEnum(_context, i.intValue());

	} else {
	    // Handle Pair
	    Pair p = (Pair)id;
	    System.out.println("FBR.PrintEnum(): Not implemented");
	}

    }

    // Compare different nodes in FBR
    public double compareEnum(Object id1, Object id2) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i1 = (Integer)id1;
	    Integer i2 = (Integer)id2;
	    return DD.CompareEnum(_context, i1.intValue(), 
				  _context, i2.intValue());

	} else {
	    // Handle Pair
	    Pair p1 = (Pair)id1;
	    Pair p2 = (Pair)id2;
	    return Double.NaN;
	}

    }

    // Compare different nodes from different FBR
    // (assuming these have same order!)
    public static double CompareEnum(FBR f1, Object n1, 
				     FBR f2, Object n2) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer
	    Integer i1 = (Integer)n1;
	    Integer i2 = (Integer)n2;
	    return DD.CompareEnum(f1._context, i1.intValue(),
				  f2._context, i2.intValue());

	} else {
	    // Handle Pair
	    Pair p1 = (Pair)n1;
	    Pair p2 = (Pair)n2;
	    return Double.NaN;
	}

    }

    //////////////////////////////////////////////////////////////////
    //                  Pruning and Approximation
    //////////////////////////////////////////////////////////////////

    // Prune nodes (keep track of min/max for for Pair).
    // Prune based on PRUNE_TYPE and PRUNE_PRECISION setting, set above.
    public Object pruneNodes(Object id) {

	if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
	    // Handle Integer

	    // Not currently implemented in DD
	    Integer i = (Integer)id;
	    return new Integer(_context.pruneNodes(i.intValue()));

	} else {
	    // Handle Pair

	    // Not currently implemented in DD
	    return null;
	}
    }

    // Class for maintaining ranges
    public class Pair {
	public Integer _o1;
	public Integer _o2;
	public Pair(Integer o1, Integer o2) {
	    _o1 = o1;
	    _o2 = o2;
	    // Set _nWhich to tell DD whether min or max?
	}
	public String toString() {
	    return "\nPAIR [ Error: " + /*_df.format(FBR.maxRange(this)) + ", " + */
		/*" Nodes: " + _context.countNodes(this, false) + */
		" ]\n\nMIN:" + _context.printNode(_o1.intValue()) + 
		"\nMAX:" + _context.printNode(_o2.intValue());
	}
    }
}
