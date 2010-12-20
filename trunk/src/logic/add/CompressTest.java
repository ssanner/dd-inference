//////////////////////////////////////////////////////////////////
//                    Testing Methods for ADD
//////////////////////////////////////////////////////////////////

package logic.add;

import graph.Graph;

import java.io.*;
import java.util.*;

// TODO: Make a version of reduce that keeps a set of previous nodes
//       encountered and merges all nodes within epsilon of a given
//       node to their average... has to preprocess in order to know
//       what nodes are available, then create a new HashMap of DNodes
//       to collapse all nodes into on a second reduce pass that does
//       the remap and reduce.  For now, skip upper and lower bound
//       approximations.  [Collect first unused node, pass through merging
//       all in with it, removing from set, and adding to HashMap].

public class CompressTest {

	public static final int    MAX_GID = 7; // 5 -- 7 produces nice viewable diagrams
	public static final double PRUNE_PRECISION = 0.1d;
	public static final int    REPLACE_TYPE = DD.REPLACE_AVG; // NO_REPLACE, REPLACE_AVG
	
	// Precision setting (1e-10 currently)
	public static final double PRECISION = AADD.PRECISION;

	// Show cache
	public static final boolean SHOW_CACHE = false;

	// Show random generator
	public static Random _rand = new Random();
	
	// Internal timing stats
	public static long _lTime;

	// General testing methods for the ADD class
	public static void main(String[] args) {
		TestCompress();
		//TestAdd();
	}

	public static void TestAdd() {

		// Prune?
		FBR.SetPruneInfo(REPLACE_TYPE, PRUNE_PRECISION);
		// FBR.SetPruneInfo(DD.REPLACE_LOW, 1e-10);

		ArrayList order = new ArrayList();
	    for (int i = 1; i <= MAX_GID; i++) {
	    	order.add(new Integer(i));
	    }
	    
	    //DD context = new Table(order);
	    DD context = new ADD(order);
	    //DD context = new AADD(order);

	    for (int i = 0; i < 1; i++) {
		    int dd1 = GetRandomizedDD(context, MAX_GID, 1 << MAX_GID);
		    int dd2 = GetRandomizedDD(context, MAX_GID, 1 << MAX_GID);
		    int ddr = context.applyInt(dd1, dd2, DD.ARITH_SUM);
		    int sz1 = (int)context.countExactNodes(dd1);
		    int sz2 = (int)context.countExactNodes(dd2);
		    int szr = (int)context.countExactNodes(ddr);
		    
			Graph g1 = context.getGraph(dd1);
			g1.launchViewer(1300, 770);
			Graph g2 = context.getGraph(dd2);
			g2.launchViewer(1300, 770);
			Graph g3 = context.getGraph(ddr);
			g3.launchViewer(1300, 770);
			//g.genDotFile("first.dot");
		    
		    System.out.println(sz1 + " + " + sz2 + " = " + szr + "  sm: " + (szr < sz1 + sz2) + " ");
		    
		    context.clearSpecialNodes();
		    context.flushCaches(false);
	    }

		//Graph g = context.getGraph(dd);
		//g.genDotFile("first.dot");
		//g.launchViewer(1300, 770);

	}
	
	public static void TestCompress() {

		// Prune?
		FBR.SetPruneInfo(REPLACE_TYPE, PRUNE_PRECISION);
		// FBR.SetPruneInfo(DD.REPLACE_LOW, 1e-10);

		// Flags: exp prod invert other sq?
		//CompareOp(true, true, false, true, false, 14, 14, "max_many_exp.txt");
	    ArrayList order = new ArrayList();
	    for (int i = 1; i <= MAX_GID + 1; i++) {
	    	order.add(new Integer(i));
	    }
	    //DD context = new Table(order);
	    //DD context = new ADD(order);
	    DD context = new AADD(order);

	    // TODO: Try adding in additional variables!!!
	    
	    int count_dd = GetCountingDD(context, MAX_GID, false); // GetCountingDD, GetExpDD, true/false
	    //int count_dd2 = GetExpDD(context, MAX_GID, false); // GetCountingDD, GetExpDD, true/false
	    //count_dd = context.applyInt(count_dd, count_dd2, DD.ARITH_SUM);
	    //int count_dd = GetExpDD(context, MAX_GID, false); // GetCountingDD, GetExpDD, true/false
	    //int count_dd = GetExpSumProdDD(context, (int)(MAX_GID/2), MAX_GID, 0.9d);
	    //int count_dd = GetExpProdDD(context, MAX_GID, 0.9d); // GetCountingProdDD, GetExpProdDD
	    System.out.println("Count DD [" + context.countExactNodes(count_dd) + "]:");
	    System.out.println(context.printNode(count_dd) + "\n");
	    //DD.PrintEnum(context,count_dd);

		Graph g3 = context.getGraph(count_dd);
		g3.genDotFile("clean.dot");
		g3.launchViewer(1300, 770);

		// AddPairNoise vs. AddAllPairNoise
	    int noise_count_dd = AddAllPairNoise(context, MAX_GID/* + 1*/, count_dd, 0.01d, false); // AddPairNoise
	    System.out.println("\n\nNoisy DD [" + context.countExactNodes(noise_count_dd) + "]:");
	    System.out.println(context.printNode(noise_count_dd) + "\n");
	    //DD.PrintEnum(context,noise_count_dd);

	    Graph g = context.getGraph(noise_count_dd);
		g.genDotFile("noisy.dot");
		g.launchViewer(1300, 770);

	    int reduce_noise_dd = context.pruneNodes(noise_count_dd);
	    //reduce_noise_dd = context.applyInt(reduce_noise_dd, reduce_noise_dd, DD.ARITH_SUM);
	    //int reduce_noise_dd2 = ((AADD)context).reduce(reduce_noise_dd);
	    System.out.println("\n\nReduced Noisy DD [" + context.countExactNodes(reduce_noise_dd) + "]:");
	    System.out.println(context.printNode(reduce_noise_dd) + "\n");
	    //DD.PrintEnum(context,reduce_noise_dd);
	    int dd_result = context.applyInt(noise_count_dd, reduce_noise_dd, DD.ARITH_MINUS);
	    System.out.println("Max approximation error: " + Math.max(Math.abs(context.getMinValue(dd_result)), 
	    							  		   Math.abs(context.getMaxValue(dd_result))));

		Graph g2 = context.getGraph(reduce_noise_dd);
		g2.genDotFile("reduced.dot");
		g2.launchViewer(1300, 770);
		//Graph g4 = context.getGraph(reduce_noise_dd2);
		//g4.launchViewer(1300, 770);

		if (SHOW_CACHE) {
		    new ADD(new ArrayList()).pruneReport();
			new AADD(new ArrayList()).pruneReport();
		}
	}
	
	// Reset the timer
	public static void ResetTimer() {
		_lTime = System.currentTimeMillis();
	}

	// Get the elapsed time since resetting the timer
	public static long GetElapsedTime() {
		return System.currentTimeMillis() - _lTime;
	}

    // Make a randomized DD 
	public static int GetRandomizedDD(DD context, int num_vars, int num_sums) {
		
		int ret = context.getConstantNode(1d);
		
		for (int i = 0; i < num_sums; i++) {
		
			int assign = _rand.nextInt(1 << num_vars);
			double val = _rand.nextDouble();
			//System.out.println(assign + ": " + val);
			ret = context.applyInt(ret, GetJointDD(context, num_vars, assign, val), DD.ARITH_SUM);
			
		}
		
		return ret;
	}
	
	public static int GetJointDD(DD context, int num_bits, int var_assign, double val) {
		int ret = context.getConstantNode(val);
		for (int i = 1; i <= num_bits; i++) {
			//System.out.println(var_assign + ": " + (var_assign % 2));
			boolean local_assign = (var_assign % 2) == 1;
			var_assign = var_assign >> 1;
			ret = context.applyInt(ret, context.getVarNode(i, local_assign ? 0d : 1d, 
					local_assign ? 1d : 0d), DD.ARITH_PROD);
		}
		return ret;
	}
	
	// Returns a counting ADD from gid 1..max_gid
	public static int GetCountingDD(DD context, int max_gid, boolean skip) {
		int ret = context.getVarNode(/* gid */1, /* low */0d, /* high */1d);
		for (int i = (skip ? 3 : 2); i <= max_gid; i += (skip ? 2 : 1)) {
			ret = context.applyInt(ret, context.getVarNode(i, 0d, 1d),
					DD.ARITH_SUM);
		}
		return ret;
	}

	// Returns an exponential coefficient ADD (a + 2b + 4c + ...) from
	// 1..max_gid
	public static int GetExpDD(DD context, int max_gid, boolean skip) {
		int ret = context.getVarNode(1, 0d, 1d);
		int coef = 1;
		for (int i = (skip ? 3 : 2); i <= max_gid; i += (skip ? 2 : 1)) {
			coef = coef << 1;
			ret = context.applyInt(ret, context.getVarNode(i, 0d, (double) coef), 
					DD.ARITH_SUM);
		}
		return ret;
	}

	// Returns a product ADD (abcd... = val) from 1..max_gid
	public static int GetCountingProdDD(DD context, int max_gid, double gamma) {
		int ret = context.getVarNode(1, 1d, Math.pow(gamma, 1d));
		for (int i = 2; i <= max_gid; i++) {
			ret = context.applyInt(ret, context.getVarNode(i, 1d, Math.pow(
					gamma, 1d)), DD.ARITH_PROD);
		}
		return ret;
	}

	// Returns a product ADD (abcd... = val) from 1..max_gid
	public static int GetExpProdDD(DD context, int max_gid, double gamma) {
		int coef = 1;
		int ret = context.getVarNode(1, 1d, Math.pow(gamma, (double) coef));
		for (int i = 2; i <= max_gid; i++) {
			coef = coef << 1;
			ret = context.applyInt(ret, context.getVarNode(i, 1d, Math.pow(
					gamma, (double) coef)), DD.ARITH_PROD);
		}
		return ret;
	}

	public static int GetExpSumProdDD(DD context, int middle_var_id, int max_var_id, double gamma) {
		
		// Build \sum_{i=1}^{middle_var_id} 2^i x_i
		int sum_dd = context.getVarNode(/* var_id */1, /* low */0d, /* high */1d);
		for (int i = 2; i <= middle_var_id; i++) {
			sum_dd = context.applyInt(sum_dd, context.getVarNode(i, 0d, 1d),
					DD.ARITH_SUM);
		}
		
		// Build \prod_{i=middle_var_id+1}^{max_var_id} \gamma^{2^i x_i}
		int coef = 1;
		int prod_dd = context.getVarNode(middle_var_id+1, 1d, 
				Math.pow(gamma, (double) coef));
		for (int i = middle_var_id+2; i <= max_var_id; i++) {
			coef = coef << 1;
			prod_dd = context.applyInt(prod_dd, context.getVarNode(i, 1d, 
					Math.pow(gamma, (double) coef)), DD.ARITH_PROD);
		}
		
		// Add them together and return
		return context.applyInt(sum_dd, prod_dd, DD.ARITH_SUM);
	}

	public static int AddPairNoise(DD context, int max_gid, int dd, 
			double noise_level, boolean rand_noise) {
		
		// Handle the wraparound pair
		int pair = context.applyInt(context.getVarNode(1, 0d, noise_level), 
				                    context.getVarNode(max_gid, 0d, 1d), DD.ARITH_PROD);
		int ret = context.applyInt(dd, pair, DD.ARITH_SUM);

		// Multiply in sequential pairs
		for (int i = 1; i < max_gid; i++) {
			pair = context.applyInt(context.getVarNode(i, 0d, 
					rand_noise ? noise_level*_rand.nextDouble() : noise_level), 
                          			context.getVarNode(i + 1, 0d, 1d), DD.ARITH_PROD);
			ret = context.applyInt(ret, pair, DD.ARITH_SUM);
		}
		return ret;
	}

	public static int AddAllPairNoise(DD context, int max_gid, int dd, 
			double noise_level, boolean rand_noise) {
	
		// Handle the wraparound pair
		int pair = context.applyInt(context.getVarNode(1, 0d, noise_level), 
				                    context.getVarNode(max_gid, 0d, 1d), DD.ARITH_PROD);
		int ret = context.applyInt(dd, pair, DD.ARITH_SUM);
		
		// Multiply in all pairs
		for (int i = 1; i <= max_gid; i++) {
			for (int j = i; j <= max_gid; j++) { 
				pair = context.applyInt(context.getVarNode(i, 0d, 
						rand_noise ? noise_level*_rand.nextDouble() : noise_level), 
	                          			context.getVarNode(j, 0d, 1d), DD.ARITH_PROD);
				ret = context.applyInt(ret, pair, DD.ARITH_SUM);
			}
		}
		return ret;
	}

	// This tests the binary operations
	public static void CompareOp(boolean exp, boolean prod, boolean invert,
			boolean other, boolean square, int table_cutoff, int aadd_cutoff,
			String outfile) {

		PrintWriter os = null;
		if (outfile != null) {
			try {
				os = new PrintWriter(new FileOutputStream(outfile));
			} catch (Exception ioe) {
			}
		}

		System.out
				.println("\nPerforming "
						+ (other ? (prod ? "*MAX* for "
								+ (square ? "[SQ] " : "") : "*OTHER* for ")
								: (invert ? "*INVERSION* of "
										: (prod ? "*PRODUCT* of " : "*SUM* of ")))
						+ (exp ? "*EXP* dd" : "*COUNTING* dd")
						+ " comparison:\n-------------------------------------------------\n");

		System.out
				.println("#vars: Table time/nodes ADD time/nodes AADD time/nodes - max diff");

		for (int mvars = 6; mvars <= aadd_cutoff; mvars += 1) {

			ArrayList order = new ArrayList();
			for (int i = 1; i <= mvars; i++) {
				order.add(new Integer(i));
			}

			DD[] dd = new DD[3];
			dd[0] = new Table(order);
			dd[1] = new ADD(order);
			dd[2] = new AADD(order);
			long[] time = new long[3];
			long[] nodes = new long[3];
			int[] ddr = new int[3];
			ddr[0] = ddr[1] = ddr[2] = DD.INVALID;

			System.out.print(mvars + ": ");

			for (int dd_type = 0; dd_type <= 2; dd_type++) {

				if (dd_type == 0 && mvars > table_cutoff) {
					continue;
				}

				// Perform DD test
				int dd1 = DD.INVALID, dd2 = DD.INVALID;

				if (exp) {
					dd1 = prod ? GetExpProdDD(dd[dd_type], mvars, 0.9999d)
							: GetExpDD(dd[dd_type], mvars, false);
					dd2 = prod ? GetExpProdDD(dd[dd_type], mvars, 0.9999d)
							: GetExpDD(dd[dd_type], mvars, false);
					// dd2 = prod
					// ? dd[dd_type].scalarMultiply(dd2, 0.9d)
					// : dd[dd_type].scalarMultiply(dd2, 2d);
				} else {
					dd1 = prod ? GetCountingProdDD(dd[dd_type], mvars, 0.999d)
							: GetCountingDD(dd[dd_type], mvars, false);
					dd2 = prod ? GetCountingProdDD(dd[dd_type], mvars, 0.999d)
							: GetCountingDD(dd[dd_type], mvars, false);
					// dd2 = prod
					// ? dd[dd_type].scalarMultiply(dd2, 0.9d)
					// : dd[dd_type].scalarMultiply(dd2, 2d);
				}

				dd[dd_type].addSpecialNode(dd1);
				dd[dd_type].addSpecialNode(dd2);
				dd[dd_type].flushCaches(false);

				ResetTimer();
				if (other) {
					if (prod) {
						dd1 = dd[dd_type].scalarMultiply(dd1, 2d);
						if (square) {
							dd1 = dd[dd_type].applyInt(dd1, dd1, DD.ARITH_PROD);
							dd2 = dd[dd_type].applyInt(dd2, dd2, DD.ARITH_PROD);
						}
						ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2,
								DD.ARITH_MAX);
					} else {
						if (square) {
							dd1 = dd[dd_type].applyInt(dd1, dd1, DD.ARITH_PROD);
						}
						dd1 = dd[dd_type].negate(dd1);
						dd1 = dd[dd_type].scalarAdd(dd1, 3d);
						ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2,
								prod ? DD.ARITH_PROD : DD.ARITH_SUM);
					}
				} else if (invert) {
					ddr[dd_type] = dd[dd_type].scalarAdd(dd1, 1.0d);
					ddr[dd_type] = dd[dd_type].invert(ddr[dd_type]);
				} else {
					ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2,
							prod ? DD.ARITH_PROD : DD.ARITH_SUM);
				}

				if (dd_type == 1 && mvars <= 5) {
					DD.PrintEnum(dd[1], dd1);
					DD.PrintEnum(dd[1], ddr[1]);
				}

				// Prune?
				// ddr[dd_type] = dd[dd_type].pruneNodes(ddr[dd_type]);
				time[dd_type] = GetElapsedTime();
				nodes[dd_type] = dd[dd_type].countExactNodes(ddr[dd_type]);
				System.out.print(time[dd_type] + "/" + nodes[dd_type] + "  ");
			}

			if (mvars <= 16) {
				System.out.println("  diff: "
						+ (mvars <= table_cutoff ? DD._df.format(DD
								.CompareEnum(dd[0], ddr[0], dd[1], ddr[1]))
								+ ", " : "")
						+ DD._df.format(DD.CompareEnum(dd[1], ddr[1], dd[2],
								ddr[2])) + " [" + DD.RUNTIME.totalMemory()
						+ "] ");
			} else {
				System.out.println();
			}

			// Output to file?
			if (os != null) {
				try {
					os.println(mvars + " " + time[0] + " " + nodes[0] + " "
							+ time[1] + " " + nodes[1] + " " + time[2] + " "
							+ nodes[2]);
				} catch (Exception ioe) {
				}
			}
		}

		if (os != null) {
			try {
				os.close();
			} catch (Exception ioe) {
			}
		}
		System.out.println();
	}
}
