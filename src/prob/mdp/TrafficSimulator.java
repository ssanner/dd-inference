package prob.mdp;

import graph.Graph;

import java.math.*;
import java.text.DecimalFormat;
import java.util.*;

import logic.add.*;

// NOTE: The only differences between this and Simulator.java are that this
//       prints the state for traffic_dual problems (4-way intersection) and it
//       always sets the stop-lights to the same legal initial state.
public class TrafficSimulator {

	/* For printing */
	public static DecimalFormat _df = new DecimalFormat("#.###");

	/* Members */
	public MDP _mdp = null;
	public ADD _context = null;
	public Object _value = null;
	public Map<String,Integer> _act2qvalue = new HashMap<String,Integer>(); // Regress Q-functions for policy evaluation
	public Map<String,Integer> _var2id = new HashMap<String,Integer>();
	public Map<Integer,String> _id2var = new HashMap<Integer,String>();
	public Map<Integer,Integer> _primeRemap = new HashMap<Integer,Integer>();
	public Map<Integer,Integer> _primeUnmap = new HashMap<Integer,Integer>();
	public ArrayList<String> _varNameList = null;
	public ArrayList<Integer> _varIDList = new ArrayList<Integer>();
	public ArrayList _internalState = new ArrayList();
	
	public Random _rand = new Random(5071978);
	
	public TrafficSimulator(String mdp_file, String value_fun_file) {
		_mdp = new MDP(HierarchicalParser.ParseFile(mdp_file), DD.TYPE_ADD);
		_context = (ADD)_mdp._context._context;
		
		ArrayList policy_list = HierarchicalParser.ParseFile(value_fun_file);
		
		// Parse the variable list and create all necessary maps
		Iterator i = policy_list.iterator();
		Object o = i.next();
		if (!(o instanceof String)
				|| !((String) o).equalsIgnoreCase("variables")) {
			System.out.println("Policy file missing variable declarations: " + o);
			System.exit(1);
		}
		o = i.next();
		int id_count = 1;
		_varNameList = (ArrayList) ((ArrayList) o).clone();
		Iterator vars = _varNameList.iterator();
		while (vars.hasNext()) {
			String vname = ((String) vars.next()) + "'";
			_id2var.put(new Integer(id_count), vname);
			_var2id.put(vname, new Integer(id_count));
			_varIDList.add(new Integer(id_count));
			++id_count;
		}
		int nvars = _varIDList.size();
		vars = _varNameList.iterator();
		while (vars.hasNext()) {
			String vname = ((String) vars.next());
			_id2var.put(new Integer(id_count), vname);
			_var2id.put(vname, new Integer(id_count));
			_varIDList.add(new Integer(id_count));
			_primeRemap.put(new Integer(id_count), new Integer(id_count	- nvars));
			_primeUnmap.put(new Integer(id_count - nvars), new Integer(id_count));
			++id_count;
		}
		
		// Quick check to make sure MDP and policy variable order matches.
		// If not, would need to choose one of them as the canonical variable
		// order.
		System.out.println("Variable Names/IDs:\n" + _varNameList);
		System.out.println(_varIDList + " == " + _mdp._alOrder);
		System.out.println("==========================================\n");
		if (_varIDList.size() != _mdp._alOrder.size()) {
			System.out.println("Variable length mismatch between MDP and policy");
			System.exit(1);
		}
		for (int j = 0; j < _varIDList.size(); j++) {
			if (!_varIDList.get(j).equals(_mdp._alOrder.get(j))) {
				System.out.println("Variable mismatch: index " + j + " " + 
						_varIDList.get(j) + " != " + _mdp._alOrder.get(j));
				System.exit(1);
			}
		}
		
		// Parse the value function
	    _value =_context.buildDDFromUnorderedTree((ArrayList)i.next(), 
			       _var2id);
		//Graph g = _context.getGraph((Integer)_value, _id2var);
		//g.launchViewer(1300, 770);
		
		// Remap the value function in terms of next state variables
		// in preparation for regression.
		int prime_value = _context.remapGIDsInt((Integer)_value, _mdp._hmPrimeRemap);
	    
		// Build Q-functions for each action from value function
		i = _mdp._hmName2Action.entrySet().iterator();
		while (i.hasNext()) {
			Map.Entry me = (Map.Entry) i.next();
			Action a = (Action) me.getValue();
			String action_name = (String) me.getKey();
			Object regr = _mdp.regress(prime_value, a, false);
			_act2qvalue.put(action_name, (Integer)regr);
		}	
		
		//Integer dia1 = _act2qvalue.get("stay");
		//Integer dia2 = _act2qvalue.get("change");
		
		//Integer diff = _context.applyInt(dia1, dia2, DD.ARITH_MINUS);
		//double max_pos_diff = _context.getMaxValue(diff);
		//double max_neg_diff = _context.getMinValue(diff);
		//System.out.println("Max difference between actions: " + 
		//		_df.format(Math.max(Math.abs(max_pos_diff), Math.abs(max_neg_diff))));

	}
	
	public void convertMapState2List(HashMap<String,Boolean> state, ArrayList list) {
		list.clear();
		for (int i = 0; i < _varNameList.size(); i++) {
			// All initial variables are primed
			list.add(null);
		}
		for (int i = 0; i < _varNameList.size(); i++) {
			Integer var_id   = _varIDList.get(i);
			String  var_name = _varNameList.get(i);
			Boolean assignment = state.get(var_name);
			//System.out.print(var_name + "[" + var_id + "] = " + assignment + " ");
			list.add(assignment);
		}

	}
	
	public void augmentStateList(ArrayList state, Integer id, boolean value) {
		// id = 4
		// state: [true false]
		// i = 2, i < 4
		// state: [true false null null]
		//        [true false null value]
		for (int i = state.size(); i < id; i++) {
			state.add(null);
		}
		state.set(id - 1, value);
	}
	
	public String getBestAction(HashMap<String,Boolean> state) {
		String best_action = null;
		double best_value = Double.NEGATIVE_INFINITY;
		for (Map.Entry<String,Integer> me : _act2qvalue.entrySet()) {
			String action  = me.getKey();
			Integer qvalue = me.getValue();
			
			// Construct state assignment
			convertMapState2List(state, _internalState);
			double value = _context.evaluate(qvalue, _internalState);
			System.out.print(", " + action + " = " + _df.format(value));
			
			if (value > best_value/*|| (value == best_value && _rand.nextBoolean())*/) {
				best_value = value;
				best_action = action;
			} 
		}
		//System.out.println("Best action:" + best_action);
		return best_action;
	}
	
	public HashMap<String,Boolean> sampleInitialState() {
		HashMap<String,Boolean> state = new HashMap<String,Boolean>();
		for (int i = 0; i < _varNameList.size(); i++) {
			String var_name = _varNameList.get(i);
			state.put(var_name, _rand.nextBoolean());
		}
		state.put("c1", true);
		state.put("c2", false);
		state.put("c3", false);
		state.put("c4", false);
		return state;
	}
	
	public HashMap<String,Boolean> sampleNextState(
			HashMap<String,Boolean> cur_state, String action) {
		
		HashMap<String,Boolean> next_state = new HashMap<String,Boolean>();
		
		Action a = (Action)_mdp._hmName2Action.get(action);
		Iterator i = a._tmID2DD.entrySet().iterator();
		while (i.hasNext()) {

			Map.Entry me = (Map.Entry) i.next();
			Integer head_id = (Integer) me.getKey();
			
			// Get the dd for this action
			Object dd = me.getValue();
			
			// Head id is a prime variable, what is the unprime version?
			Integer next_state_id = _primeUnmap.get(head_id);
			
			// Need to find probability it is true, given state
			convertMapState2List(cur_state, _internalState);
			augmentStateList(_internalState, head_id, true);
			double prob = _context.evaluate((Integer)dd, _internalState);
			
			//Graph g = _context.getGraph((Integer)dd, _id2var);
			//g.launchViewer(1300, 770);
			
			// Then sample from probability and make assignment in next_state
			//System.out.println(_id2var.get(head_id) + "[" + _df.format(prob) + "] = eval: " + cur_state);
			next_state.put(_id2var.get(next_state_id), _rand.nextDouble() < prob);
		}		
		return next_state;
	}

	public String getTrafficString(HashMap<String,Boolean> state) {
		
		//  r6 r4 r2  TG  ||  RN  r1 r3 r5
		StringBuilder sb = new StringBuilder();
		int max_size = (_varNameList.size() - 8)/4;
		for (int i = max_size; i >= 1; i--) {
			boolean val = state.get("r" + (i << 1));
			sb.append(val ? "." : "#");
		}
		
		sb.append(" " +  (state.get("t2") ? "T" : "N") + 
				         (state.get("c2") ? "G" : "R") + " |");
		
		sb.append("| " + (state.get("t1") ? "T" : "N") + 
		                 (state.get("c1") ? "G" : "R") + " ");
				
		for (int i = 1; i <= max_size; i++) {
			boolean val = state.get("r" + ((i << 1) - 1));
			sb.append(val ? "." : "#");
		}		
		
		//  r6 r4 r2  TG  ||  RN  r1 r3 r5
		StringBuilder sb2 = new StringBuilder();
		for (int i = max_size; i >= 1; i--) {
			boolean val = state.get("q" + (i << 1));
			sb2.append(val ? "." : "#");
		}
		
		sb2.append(" " + (state.get("t4") ? "T" : "N") + 
				         (state.get("c4") ? "G" : "R") + " |");
		
		sb2.append("| " + (state.get("t3") ? "T" : "N") + 
		                  (state.get("c3") ? "G" : "R") + " ");
				
		for (int i = 1; i <= max_size; i++) {
			boolean val = state.get("q" + ((i << 1) - 1));
			sb2.append(val ? "." : "#");
		}		
	
		return sb.toString() + "\n" + sb2.toString() + "\n";
	}
	
	public static class SimResult {
		double _mean, _std, _std_error;
		public SimResult(double mean, double std, double std_error) {
			_mean = mean; _std = std; _std_error = std_error;
		}
		public String toString() {
			return _df.format(_mean) + " +/- " + _df.format(_std_error) 
					+ ", " + _df.format(_std);
		}
	}
	
	public SimResult simulate(int num_samples, int traj_length) {
		
		double[] samples = new double[num_samples]; 
		double[] values  = new double[traj_length + 1];
		double accum = 0d;
		HashMap<String,Boolean> cur_state;
		for (int i = 0; i < num_samples; i++) {
			
			System.out.println("============ [ Begin Trial #" + (i+1) /*+ "/" + num_samples*/ + " ] ============\n");
			
			cur_state = sampleInitialState();
			convertMapState2List(cur_state, _internalState);
			values[0] = _context.evaluate((Integer)_mdp._rewardDD, _internalState);
			
			System.out.println("   -->          <--");
			System.out.print(getTrafficString(cur_state) + "  [" + 
					_df.format(values[0]) + "] ");
			
			for (int j = 1; j <= traj_length; j++) {
				
				String best_action = getBestAction(cur_state);
				cur_state          = sampleNextState(cur_state, best_action);
				
				convertMapState2List(cur_state, _internalState);
				values[j] = _context.evaluate((Integer)_mdp._rewardDD, _internalState);
				
				System.out.println(" -> " + best_action);
				System.out.print(getTrafficString(cur_state) + "  [" + 
						_df.format(values[j]) + "] ");
			}

			System.out.println("\n\n============= [ End Trial #" + i + " ] =============");
			
			samples[i] = computeEDR(values, _mdp._bdDiscount.doubleValue());
			accum += samples[i];
		}
		
		double mean = accum / (double)num_samples;
		double std  = computeStd(samples, mean);
		double std_error = std / Math.sqrt((double)num_samples);
		return new SimResult(mean, std, std_error);
	}
	
	public double computeStd(double[] values, double mean) {
		double accum = 0d;
		for (int i = 0; i < values.length; i++) {
			double diff = (values[i] - mean);
			accum += diff * diff;
		}
		return Math.sqrt(accum / (double)(values.length - 1));
	}
	
	public double computeEDR(double[] values, double discount) {
		double accum = 0;
		double cur_discount = 1d;
		for (int i = 0; i < values.length; i++) {
			accum += cur_discount * values[i];
			cur_discount *= discount;
		}
		return accum;
	}
	
	/**
	 * Basic testing interface.
	 **/
	public static void main(String args[]) {
		if (args.length != 4) {
			System.out.println("\nMust enter MDP-filename, "
							+ "policy_dd, num_samples, traj_length\n");
			System.exit(1);
		}

		// Parse problem filename
		String mdp_file       = args[0];
		String value_fun_file = args[1];

		// Parse prune precision and type
		int num_samples = -1;
		int traj_length = -1;
		try {
			num_samples = (new Integer(args[2]));
			traj_length = (new Integer(args[3]));
		} catch (NumberFormatException nfe) {
			System.out.println("\nIllegal precision specification\n");
			System.exit(1);
		}

		// Set up FBR for all operations, interpret prune_prec as percent
		// of total reward (so 10 = 10% of MR:8 = .8)
		TrafficSimulator s = new TrafficSimulator(mdp_file, value_fun_file);
		SimResult r = s.simulate(num_samples, traj_length);
		System.out.println("\nSimulator results: " + r);
	}
}
