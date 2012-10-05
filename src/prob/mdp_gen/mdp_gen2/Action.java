//////////////////////////////////////////////////////////////////////
//
// File:     Action.java
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
// Requires: comshell package
//
// Description:
//
//   Class for action representation/construction.
//
//////////////////////////////////////////////////////////////////////

// Package definition
package prob.mdp_gen;

// Packages to import
import java.io.*;
import java.util.*;
import logic.add_gen.*;

/**
 * Class for action representation/construction.
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class Action
{
    /* Local constants */

    /* Local vars */
    public MDP_Gen       _mdp;     // MDP of which this action is a part
    public String    _sName;   // Name of this action
    public int       _nDDType; // Type of DD (see MDP)
    public TreeMap   _tmID2DD; // Maps next-state ID to a CPT decision diagram (DD)
    public HashSet   _hsTransDDs;

    /** Constructor
     **/
    public Action(MDP_Gen mdp, String name, HashMap cpt_desc) {
	
	_mdp     = mdp;
	_sName   = name;
	_nDDType = mdp._nDDType;
	_tmID2DD = new TreeMap();
	_hsTransDDs = new HashSet();
	buildAction(cpt_desc);
    }

    /** Build action description DDs
     **/
    public void buildAction(HashMap cpt_desc) {

	// Head will be for current next-state
	Iterator entries = cpt_desc.entrySet().iterator();
	while (entries.hasNext()) {

	    // Get head variable and high-side decision diagram
	    Map.Entry me = (Map.Entry)entries.next();
	    Integer headID = (Integer)_mdp._tmVar2ID.get(((String)me.getKey()));

	    // Now build up high and low-side prob decision diagram
	    //System.out.println(me.getValue());
	    Object phead_true = _mdp._context.buildDDFromUnorderedTree((ArrayList)me.getValue(), 
								       _mdp._tmVar2ID);
	    Object phead_false = _mdp._context.applyInt(_mdp._context.getConstantNode(1d),
						       phead_true, DD.ARITH_MINUS);
	    
	    // Get the var DD
	    Object high_br = _mdp._context.getVarNode(headID.intValue(), 0.0d, 1.0d);
	    high_br = _mdp._context.applyInt(high_br, phead_true,
					     DD.ARITH_PROD);

	    // Get the !var ADD
	    Object low_br  = _mdp._context.getVarNode(headID.intValue(), 1.0d, 0.0d);
	    low_br = _mdp._context.applyInt(low_br, phead_false,
					    DD.ARITH_PROD);

	    // Compute final dd
	    Object final_dd = _mdp._context.applyInt(low_br, high_br, DD.ARITH_SUM);
	    _hsTransDDs.add(final_dd);
	    
	    // Set this final DD
	    if (DD.PRUNE_TYPE != DD.REPLACE_RANGE) {
		_tmID2DD.put(headID, final_dd);
	    } else {
		System.out.println("Action: Pair not implemented");
		System.exit(1);
		//System.out.println("Pruning action '" + _sName
		//		   + "', DBN node " + headID + "...");
		//FBR.Pair p = new FBR.Pair(final_dd, final_dd);
		//FBR.pruneNodes(p);
		//_tmID2DD.put(headID, p);
	    }
	}
    }

    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append(_sName + ":\n");
	Iterator i = _tmID2DD.entrySet().iterator();
	while (i.hasNext()) {
	    Map.Entry me = (Map.Entry)i.next();
	    sb.append(me.getKey() + " ->\n");
	    sb.append(_mdp._context.printNode(me.getValue()) + "\n");
	    sb.append(_mdp._context.printNode(_mdp._context.opOut(me.getValue(), 
					   ((Integer)me.getKey()).intValue(), DD.ARITH_SUM)) + "\n");
	}
	return sb.toString();
    }
}
