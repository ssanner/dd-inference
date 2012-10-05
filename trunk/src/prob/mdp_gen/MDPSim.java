//////////////////////////////////////////////////////////////////////////
//
// File:     MDPSim.java
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
//
// Description:
//
//   Simulator for an MDP.     ***MDP.FLUSH_CACHES must be false***
//
//////////////////////////////////////////////////////////////////////////

// Package definition
package prob.mdp_gen;

// Packages to import
import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

// DD & FBR interfaces
import logic.add_gen.*;

/**
 * Main MDPSim inference class
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class MDPSim
{
    //public final static double W_BASIS_1 = 1d; 
    //public final static double W_BASIS_2 = 1d; 
    public final static double W_BASIS_1 = 0.050d; 
    public final static double W_BASIS_2 = 0.098d; 

    public int _nVars = -1;
    public MDP_Gen _mdp;
    public TreeSet _vars;
    public ArrayList _state;
    public HashMap _qfuns;
    public Boolean TRUE  = new Boolean(true);
    public Boolean FALSE = new Boolean(false);
    public Random _r;
    public boolean _bUseBasis;

    // Build the MDP and value function, as well as the Q-functions for
    // executing the greedy policy.
    public MDPSim(String prob_file, String vfun_file) {
	_mdp = new MDP_Gen(prob_file, DD.TYPE_ADD);
	_bUseBasis = vfun_file.equalsIgnoreCase("basis");
	if (_bUseBasis) {
	    _mdp._valueDD = null;
	} else {
	    _mdp._valueDD = _mdp._context.buildDDFromUnorderedTree(MDPConverter.ADDFileToTree(vfun_file), 
								   _mdp._tmVar2ID);
	
	    _qfuns = new HashMap();
	    Iterator i = _mdp._hmName2Action.entrySet().iterator();
	    while (i.hasNext()) {
		
		Map.Entry me = (Map.Entry)i.next();
		Action a = (Action)me.getValue();
		
		//////////////////////////////////////////////////////////////
		// Regress the current value function through each action
		//////////////////////////////////////////////////////////////
		Object qfun = _mdp.regress(_mdp._context.remapGIDsInt(_mdp._valueDD, _mdp._hmPrimeRemap), a);
		System.out.println("Calculating Q-function for action: " + a._sName);
		//System.out.println(_mdp._context.printNode(qfun) + "\n");
		
		_qfuns.put(a._sName, qfun);
	    }
	} 
	System.out.println(_mdp);
    }

    // Derives QFunctions for the given value function and simulates the
    // greedy policy for the given number of trials and steps per trial.
    // Returns final value of every trial.
    public ArrayList simulate(int trials, int steps, long rand_seed) {
	ArrayList values = new ArrayList();
	_r = new Random(rand_seed);

	for (int trial = 1; trial <= trials; trial++) {
	    
	    System.out.println("\n -----------\n   Trial " + trial + "\n -----------");

	    // Initialize state
	    _state = new ArrayList();
	    _nVars = _mdp._alVars.size();
	    for (int c = 0; c < (_nVars << 1); c++) {
		_state.add("-");
	    }
	    Iterator i = _mdp._alVars.iterator();
	    _vars = new TreeSet();
	    while (i.hasNext()) {
		String s = (String)i.next();
		if (!s.endsWith("\'")) {
		    Integer gid = (Integer)_mdp._tmVar2ID.get(s); 
		    _vars.add(gid);

		    // Note: assign level (level is gid-1 b/c gids in order)
		    _state.set(gid.intValue() - 1, _r.nextBoolean() ? TRUE : FALSE);
		}
	    }
	    //System.out.println(_mdp._context.printNode(_mdp._valueDD) + "\n" + _state);
	    double reward = _mdp._context.evaluate(_mdp._rewardDD, _state);
	    System.out.print(" " + PrintState(_state) + 
			       "  " + MDP_Gen._df.format(reward));		

	    // Run steps
	    for (int step = 1; step <= steps; step++) {

		// Get action
		Action a;
		if (_bUseBasis) {
		    a = getBasisAction();
		} else {
		    a = getAction();
		}

		// Execute action
		executeAction(a);

		// Update reward
		reward = (_mdp._bdDiscount.doubleValue() * reward) + 
		         _mdp._context.evaluate(_mdp._rewardDD, _state);
		
		System.out.println(", a=" + a._sName);
		System.out.print(" " + PrintState(_state) + "  " + MDP_Gen._df.format(reward) + ": " +
				 "Step " + step);		
	    }
	    values.add(new Double(reward));
	    System.out.println();
	}
	
	return values;
    }

    // Determines the best action, given the Q-functions
    public Action getAction() {

	Iterator i = _qfuns.keySet().iterator();
	Action best_act = null;
	double best_val = -1d;
	while (i.hasNext()) {
	    
	    String act_name = (String)i.next();
	    Object qfun = _qfuns.get(act_name);
	    Action a = (Action)_mdp._hmName2Action.get(act_name);
	    double val = _mdp._context.evaluate(qfun, _state);

	    //System.out.println(a._sName + " -> " +_mdp._context.printNode(qfun));
	    //System.out.println("  " + a._sName + " -> " + _mdp._df.format(val));
	    if (val > best_val) {
		best_act = a;
		best_val = val;
	    }
	}	
	//System.out.println("  Chose: " + best_act._sName);

	return best_act;
    }

    // Fill in weights for specific counting aggregator approaches
    //
    // Basis function 1: Count of computers running
    // Basis function 2: Count of computers running and connected to
    //                   one other running computer
    //
    // Assuming action succeeds... compute next-state value based on action, 
    // choose best action.
    public Action getBasisAction() {

	int best_reboot = -1;
	double best_reboot_val = -1d;
	for (int c = 1; c <= _nVars; c++) {
	   ArrayList test_state = (ArrayList)_state.clone();
	   test_state.set(c - 1 + _nVars, TRUE);
	   double test_val = evalBasisState(test_state, 
					    W_BASIS_1,
					    W_BASIS_2);
	   if (test_val > best_reboot_val) {
	       best_reboot_val = test_val;
	       best_reboot = c;
	   }
	}

	return (Action)_mdp._hmName2Action.get("reboot" + best_reboot);
    }

    public double evalBasisState(ArrayList state, double wb1, double wb2) {

	int sum_basis_1 = 0;
	int sum_basis_2 = 0;

	// TODO: Code to get connection links... use current state to get status
	//System.out.print(", Eval: " + state);
	Action a = (Action)_mdp._hmName2Action.get("noreboot");
	for (int c = 0; c < (_nVars << 1); c++) {
	    Object cur_assign = state.get(c);
	    if (cur_assign instanceof Boolean && 
		((Boolean)cur_assign).booleanValue()) {

		sum_basis_1++;

		//System.out.println(a._tmID2DD);
		int nonprime_id = c + 1;
		int prime_id = nonprime_id - _nVars;
		Object DD = a._tmID2DD.get(new Integer(prime_id));
		Set IDs = _mdp._context.getGIDs(DD);
		//System.out.print(IDs + ": ");
		Iterator it = IDs.iterator();
		//System.out.print("[" + prime_id + " - ");
		while (it.hasNext()) {
		    int c_id = ((Integer)it.next()).intValue() - 1; // nonprime array index
		    if (c_id < _nVars || c_id == c) { // Skip prime/np this var
			continue;
		    }
		    //System.out.print(c_id + " ");
		    Object c_id_assign = state.get(c_id);
		    if (c_id_assign instanceof Boolean && 
			((Boolean)c_id_assign).booleanValue()) {
			sum_basis_2++;
			break;
		    }
		}
		//System.out.println("]");
	    }
	}
	double val = wb1 * sum_basis_1 + wb2 * sum_basis_2;
	//System.out.println(state + ", b1: " + sum_basis_1 + 
	//		   ", b2: " + sum_basis_2 + ", total: " + 
	//		   _mdp._df.format(val));

	return val;	
    }

    // Executes the given action
    public void executeAction(Action a) {

	// For each state variable, retrieve the DD for it, evaluate it
	// w.r.t. the current state and build a new state.
	ArrayList new_state = new ArrayList();
	int c;
	for (c = 0; c < (_nVars << 1); c++) {
	    new_state.add("-");
	}
	for (c = 0; c < (_nVars << 1); c++) {
	    Object cur_assign = _state.get(c);
	    if (cur_assign instanceof Boolean) {
			//System.out.println(a._tmID2DD);
			int nonprime_id = c + 1;
			int prime_id = nonprime_id - _nVars;
			Object DD = a._tmID2DD.get(new Integer(prime_id));
			_state.set(prime_id - 1, TRUE);
			double p_true = _mdp._context.evaluate(DD, _state);
			//System.out.println("ID: " + nonprime_id + ", " + prime_id + ": " + 
			//		   _mdp._context.printNode(DD) + " -> " + 
			//		   _mdp._df.format(p_true));
			new_state.set(c, (_r.nextFloat() < p_true) ? TRUE : FALSE);
	    }
	}

	_state = new_state;
    }

    ////////////////////////////////////////////////////////////////////////////////////
    //                                Helper Functions
    ////////////////////////////////////////////////////////////////////////////////////

    public static String PrintState(ArrayList state) {
	StringBuffer sb = new StringBuffer();
	Iterator i = state.iterator();
	while (i.hasNext()) {
	    Object o = i.next();
	    if (o instanceof Boolean) {
		Boolean val = (Boolean)o;
		sb.append((val.booleanValue() ? "." : "X"));
	    }
	}
	return sb.toString();
    }

    public static String PrintList(ArrayList l) {
	StringBuffer sb = new StringBuffer("[ ");
	Iterator i = l.iterator();
	while (i.hasNext()) {
	    Double d = (Double)i.next();
	    sb.append(MDP_Gen._df.format(d.doubleValue()) + " ");
	}
	sb.append("]");
	return sb.toString();
    }

    public static double Average(ArrayList l) {
	double accum = 0.0d;
	Iterator i = l.iterator();
	while (i.hasNext()) {
	    Double d = (Double)i.next();
	    accum += d.doubleValue();
	}
	return (accum / (double)l.size());
    }

    ////////////////////////////////////////////////////////////////////////////////////
    //                                    Main Routine
    ////////////////////////////////////////////////////////////////////////////////////

    public static void main(String[] args) {
	if (args.length < 5) {
	    System.out.println("\n  Usage: java prob.mdp.MDPSim prob_file " + 
			       "spudd_vfun trials steps rand_seed\n");
	    System.exit(1);
	} 

	MDPSim mdpsim = new MDPSim(args[0], args[1]);
	
	ArrayList vals = null;
	int trials = -1, steps = -1;
	long seed = -1;
	try {
	    trials = Integer.parseInt(args[2]);
	    steps  = Integer.parseInt(args[3]);
	    seed   = Long.parseLong(args[4]);
	    vals = mdpsim.simulate(trials, steps, seed);
	} catch (NumberFormatException nfe) {
	    System.out.println(nfe);
	    System.exit(1);
	}

	System.out.println("\n Problem:  " + args[0]);
	System.out.println(" VFun:     " + args[1]);
	System.out.println(" Trials:   " + trials);
	System.out.println(" Steps:    " + steps);
	System.out.println(" Seed:     " + seed);
	System.out.println(" Data:     " + PrintList(vals));
	System.out.println(" Average:  " + MDP_Gen._df.format(Average(vals)) + "\n");
    }
}
