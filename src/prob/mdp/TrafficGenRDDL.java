//////////////////////////////////////////////////////////////////////
//
// File:     MDP.java
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
// Requires: comshell package
//
// Description:
//
//   Generates network problems.
//
// TODO:
//
//   Should have a generator for both tree readers and ADD/AADD readers.
//
//////////////////////////////////////////////////////////////////////

// Package definition
package prob.mdp;

// Packages to import
import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;
import logic.add.*;

/**
 * Generates network problems from a HashMap of ID's and connections
 * 
 * @version 1.0
 * @author Scott Sanner
 * @language Java (JDK 1.3)
 **/
public class TrafficGen {
	public static boolean PERTURB_REWARD = false;

	/** Constants **/
	public static final double PROB_TURN   = 0.8;
	public static final double PROB_ARRIVE_1 = 0.5;
	public static final double PROB_ARRIVE_2 = 0.8;
	
	/** For printing **/
	public static DecimalFormat _df = new DecimalFormat("#.###");

	/** Generator **/
	public static void GenTrafficFile(int size) {

		System.out.println("\nGenerating Traffic: " + size);
		if (size < 3) {
			System.out.println("TrafficGen: Size must be at least 3.");
			System.exit(1);
		}
		String filename = "traffic" + size + ".spudd";
		PrintWriter os = null;
		try {
			// Open the output file
			os = new PrintWriter(new FileOutputStream(filename));

			// Get all ids and print them to the file
			ArrayList<String> var_order = new ArrayList<String>();
			TreeSet<String> road_cell_ids = new TreeSet<String>();
			var_order.add("c1");
			var_order.add("c2");
			for (int i = size << 1; i >= 1 ; i--) {
				road_cell_ids.add("r" + i);
				var_order.add("r" + i);
			}
			var_order.add("t1");
			var_order.add("t2");
			TreeSet<String> ids = new TreeSet<String>(var_order);

			os.print("variables ( ");
			for (String var : var_order) {
				os.print(var + " ");
			}
			os.println(")");

			// Generate order and ADD
			HashMap<String,Integer> var2id = new HashMap<String,Integer>();
			HashMap<Integer,String> id2var = new HashMap<Integer,String>();
			ArrayList order = new ArrayList();
			int id = 1;
			for (String var : ids) {
				var2id.put(var, id);
				id2var.put(id, var);
				order.add(id);
				++id;
			}
			ADD context = new ADD(order);

			// Generate generic noreboot
			boolean[] actions = new boolean[] { false, true };

			// TODO: incorporate multiple traffic directions!
			//       N,S,E,W!
			
			// TODO: need general intersection description
			//       need general rules description for behavior
			//       need a compiler to generate factored MDP from
			//            both of the above
			
			// First generate
			for (boolean b : actions) {
				
				// Generate light change: c1, c2
				if (b) { // stay
					os.println("action stay");
					System.out.println(" - Action: stay");
					os.println("c1 (c1 (1.0) (0.0))");					
					os.println("c2 (c2 (1.0) (0.0))");
					
				} else { // change
					os.println("action change");
					// 00
					// 01
					// 11
					// 10
					System.out.println(" - Action: change");
					os.println("c1 (c2 (1.0) (0.0))");
					os.println("c2 (c1 (0.0) (1.0))");
				}
				
				// Generate lane turn update: t1, t2
				// Note: r1 = T means "unoccupied"
				os.println("t1 (r1 (" + _df.format(PROB_TURN) + ")");					
				os.println("       (t1 (1.0) (0.0)))");					
				os.println("t2 (r2 (" + _df.format(PROB_TURN) + ")");					
				os.println("       (t2 (1.0) (0.0)))");					
				
				// Generate intersection road cell: r1, r2
				// TODO: incorporate random braking
				// TODO: turning should look even farther back than first car
				os.println("r1 (c1 (r1 (r3 (1.0) (0.0))");					
				os.println("           (t1 (r2 (1.0) (c2 (t2 (1.0) (0.0)) ");
				os.println("                             (1.0))");					
				os.println("                   (1.0))");
				os.println("               (1.0)))");
				os.println("       (r1 (r3 (1.0) (0.0)) (0.0)))");
				
				os.println("r2 (c2 (r2 (r4 (1.0) (0.0))");					
				os.println("           (t2 (r1 (1.0) (c1 (t1 (1.0) (0.0)) ");
				os.println("                             (1.0))");					
				os.println("                   (1.0))");
				os.println("               (1.0)))");
				os.println("       (r2 (r4 (1.0) (0.0)) (0.0)))");
				
				// Generate intermediate road cell: r2, r3, ... , r(size-2), r(size-1)
				String interm_road_cell1 =
					"r3 (r3 (r5 (1.0) (0.0))\n" +
					"       (r1 (1.0) (0.0)))";
				String interm_road_cell2 = interm_road_cell1.
					replace("r1 ", "r2 ").replace("r3 ", "r4 ").replace("r5 ", "r6 ");
				os.println(interm_road_cell1);
				os.println(interm_road_cell2);
				for (int i = 5; i <= (size << 1) - 2; i+=2) {
					os.println(interm_road_cell1.
							replace("r5 ", "r"+(i+2)+" ").replace("r3 ", "r"+i+" ").replace("r1 ", "r"+(i-2))+" ");
					os.println(interm_road_cell2.
							replace("r6 ", "r"+(i+3)+" ").replace("r4 ", "r"+(i+1)+" ").replace("r2 ", "r"+(i-1))+" ");
				}
				
				// Generate feeder road cell: r(size), r(size+1)
				int o = (size << 1) - 1;
				int e = size << 1;
				os.println("r"+o+" (r"+(o-2)+" (" + _df.format(1d-PROB_ARRIVE_1) + ")");					
				os.println("       (r"+o+" (" + (1d-PROB_ARRIVE_1) + ") (0.0)))");			
				os.println("r"+e+" (r"+(e-2)+" (" + _df.format(1d-PROB_ARRIVE_2) + ")");					
				os.println("       (r"+e+" (" + (1d-PROB_ARRIVE_2) + ") (0.0)))");			
				
				os.println("endaction");
			}
			
			// Generate reward
			// TODO: Penalize inter-green in reward
			os.print("reward ");
			int rew = GetCountingDD(context, road_cell_ids, 0d, var2id);
			context.dumpToTree(rew, id2var, os, _df, 0);

			// Generate discount and tolerance
			os.println("\n\ndiscount 0.990000");
			os.println("tolerance 0.010000");

			// Close file
			os.close();

		} catch (IOException ioe) {
			System.out.println(ioe);
			System.exit(1);
		}
	}

	// Returns a counting ADD from gid 1..max_gid
	public static int GetCountingDD(DD context, Set<String> vars, double off,
			HashMap<String,Integer> var2id) {
		// System.out.println("GETCD: " + vars + ", " + context._alOrder);
		int ret = context.getConstantNode(off);
		for (String var : vars) {
			int var_id = var2id.get(var);
			ret = context.applyInt(ret, context.getVarNode(var_id, 0d, 1d), 
					DD.ARITH_SUM);
		}
		return ret;
	}

	/** Main **/
	public static void main(String[] args) {
		if (args.length != 0) {
			System.out.println("java prob.mdp.TrafficGen");
			System.exit(1);
		} 

		GenTrafficFile(3);
		GenTrafficFile(4);
		GenTrafficFile(5);
		GenTrafficFile(6);
		GenTrafficFile(7);
		GenTrafficFile(8);
		GenTrafficFile(9);
		GenTrafficFile(10);
	}

}
