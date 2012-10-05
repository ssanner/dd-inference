//////////////////////////////////////////////////////////////////
//                    Testing Methods for ADD
//////////////////////////////////////////////////////////////////

package logic.add_gen;

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

	public static final int    MAX_GID = 20; // 5 -- 7 produces nice viewable diagrams
	public static final double PRUNE_PRECISION = 1d;
	public static final int    REPLACE_TYPE = DD.REPLACE_AVG; // NO_REPLACE, REPLACE_AVG
	
	public static final boolean DRAW = true;
	
	public static final boolean EN_TABLE = false;
	public static final boolean EN_ADD = false;
	public static final boolean EN_AADD_SD = true;
	public static final boolean EN_AADD_DD = true;
	public static final boolean EN_AADD_LD = true;
	
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
//		TestCompress();
		//TestAdd();
//		CompareOp(b exp, b prod, b invrt,b otr, b sqr, i tbct,i add_ct, i aadd_ct,
//				String outfile)
		CompareOp(false,true,true,true,true,18,15,18,"Hollow");
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
	    ArrayList order = new ArrayList();
	    for (int i = 1; i <= MAX_GID; i++) order.add(new Integer(i));
	    int N_OP = 1;
	    
	    if (EN_TABLE) {	DD context1 = new Table(order);makeTestDD(context1,N_OP,1);}
	    
	    if (EN_ADD){DD context2 = new ADD(order);makeTestDD(context2,N_OP,2);}
	    
	    if (EN_AADD_SD){
	    	DD context3 = new AADD(order,AADD.SIMPLEDOUBLE);
//	    	context3.showCacheSize();
	    	makeTestDD(context3,N_OP,3);
//	    	context3.showCacheSize();
	    }
	    
	    if (EN_AADD_DD){
	    	DD context4 = new AADD(order,AADD.DOUBLEDOUBLE);
	    	makeTestDD(context4,N_OP,4);
	    }
	    if (EN_AADD_LD){
	    	DD context5 = new AADD(order,AADD.LOGDOUBLE);
	    	makeTestDD(context5,N_OP,5);
	    }	    
	    
	    DD context6 = new DAADD(order);
	    	makeTestDD(context6,N_OP,1);
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
		return GetCountingDD(context, max_gid, skip,0d,1d);
	}	

	public static int GetCountingDD(DD context, int max_gid, boolean skip,double low,double high) {
		int ret = context.getVarNode(/* gid */1, low, high);
		for (int i = (skip ? 3 : 2); i <= max_gid; i += (skip ? 2 : 1)) {
			ret = context.applyInt(ret, context.getVarNode(i, low, high),
					DD.ARITH_SUM);
		}
		return ret;
	}

	// Returns an exponential coefficient ADD (a + 2b + 4c + ...) from
		// 1..max_gid
	public static int GetExpDD(DD context, int max_gid, boolean skip) {
		return GetExpDD(context, max_gid, skip, 0d,1d);
	}
	// Returns an exponential coefficient ADD (low + a(high-low) + low+b(2high-low) + ...) from
	// 1..max_gid
	public static int GetExpDD(DD context, int max_gid, boolean skip,double low,double high) {
		int ret = context.getVarNode(1, low, high);
		int coef = 1;
		for (int i = (skip ? 3 : 2); i <= max_gid; i += (skip ? 2 : 1)) {
			coef = coef << 1;
			ret = context.applyInt(ret, context.getVarNode(i, low, high* (double) coef), 
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

	// Returns a product ADD (ab^2c^3d^4... = val) from 1..max_gid
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
		
		// Build \sum_{i=1}^{middle_var_id}
		int sum_dd = context.getVarNode(/* var_id */1, /* low */0d, /* high */1d);
		for (int i = 2; i <= middle_var_id; i++) {
			sum_dd = context.applyInt(sum_dd, context.getVarNode(i, 0d, 1d),
					DD.ARITH_SUM);
		}
		
		//Build \prod_{i=1}^{max_var_id-middle_var_id} 2^i x_(middle_var_id+i)
		// not Build \prod_{i=middle_var_id+1}^{max_var_id} \gamma^{2^i x_i}
		int coef = 1;// 1 << middle_var_id for kind 2
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
		int pair = context.applyInt(context.getVarNode(1, 0d, 
					rand_noise ? noise_level*_rand.nextDouble() : noise_level), 
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
			boolean other, boolean square, int table_cutoff,int add_cutoff, int aadd_cutoff,
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

			DD[] dd = new DD[6];
			dd[0] = new Table(order);
			dd[1] = new ADD(order);
			dd[2] = new AADD(order,AADD.SIMPLEDOUBLE);
			dd[3] = new AADD(order,AADD.DOUBLEDOUBLE);
			dd[4] = new AADD(order,AADD.LOGDOUBLE);
			dd[5] = new DAADD(order);
			long[] time = new long[6];
			long[] nodes = new long[6];
			int[] ddr = new int[6];
			ddr[0] = ddr[1] = ddr[2] = ddr[3] = ddr[4] = ddr[5] = DD.INVALID;

			System.out.print(mvars + ": ");

			for (int dd_type = 0; dd_type <= 5; dd_type++) {

				if (dd_type == 0 && mvars > table_cutoff) {
					continue;
				}
				if (dd_type == 1 && mvars > add_cutoff) {
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

			if (mvars <= aadd_cutoff) {
				System.out.println("  diff: "
						+ (mvars <= table_cutoff ? DD._df.format(DD
								.CompareEnum(dd[0], ddr[0], dd[1], ddr[1]))
								+ ", " : "")
						+ DD._df.format(DD.CompareEnum(dd[5], ddr[5], dd[2],
								ddr[2])) + ", "
						+ DD._df.format(DD.CompareEnum(dd[5], ddr[5], dd[3],
										ddr[3])) + ", "
						+ DD._df.format(DD.CompareEnum(dd[5], ddr[5], dd[4],
								ddr[4])) + ", " 
						+ DD._df.format(DD.CompareEnum(dd[5], ddr[5], dd[1],
								ddr[1])) +  " [" + DD.RUNTIME.totalMemory()
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
	
    public static int operateMany(DD context, int topNode, int op, int numOps, int tgt){
    	int temp = topNode;
    	for (int i = 0; i < numOps; i++){
    		temp = context.applyInt(temp, tgt, op);
    	}
    	return temp;
    }

    public static int makeProdTestDD(DD context, int numOps){
	    int cprod_dd = GetCountingProdDD(context, MAX_GID,2); // GetCountingDD, GetExpDD, true/false
	    int expprod_dd = GetExpProdDD(context, MAX_GID,1.02); // GetCountingDD, GetExpDD, true/false
	    int expprod_dd2 = GetExpProdDD(context, MAX_GID-3,1.0003); // GetCountingDD, GetExpDD, true/false
	    int temp = operateMany(context, cprod_dd, DD.ARITH_PROD, numOps, expprod_dd);
	    temp = operateMany(context, temp, DD.ARITH_DIV, numOps, expprod_dd2);
	    temp = operateMany(context, temp, DD.ARITH_DIV, numOps, expprod_dd);
	    int res = operateMany(context, temp, DD.ARITH_PROD, numOps, expprod_dd2);
	    return res;
    }
    
    public static int makeSimpleTestDD(DD context, int numOps){
    int Op = DD.ARITH_SUM;
    int cprod_dd = GetCountingDD(context, MAX_GID,false); // GetCountingDD, GetExpDD, true/false
    int temp = operateMany(context, cprod_dd, Op, numOps, cprod_dd);
    return temp;
}
    
    public static int makeTestDD(DD context, int numOps,int n){
    ResetTimer();
    int temp = makeSumTestDD(context, numOps);
    System.out.println("Simple Test: AADTYPE="+getKind(context)+" OpTime: "+GetElapsedTime()+" Nodes = "+ context.countExactNodes(temp));
    if (DRAW){
    	Graph g = context.getGraph(temp);
    	g.genDotFile("clean"+n+".dot");
    	g.launchViewer(1300, 770);
//    	context.pruneReport();
    }
    return temp;
}

    
    public static int makeSumTestDD(DD context, int numOps){
	    int cprod_dd = GetCountingDD(context, MAX_GID,false,1d,2d); // GetCountingDD, GetExpDD, true/false
	    int expprod_dd = GetExpDD(context, MAX_GID,false,1d,3d); // GetCountingDD, GetExpDD, true/false
	    int expprod_dd2 = GetExpDD(context, MAX_GID,false,1d,2d); // GetCountingDD, GetExpDD, true/false
	    int temp = operateMany(context, cprod_dd, DD.ARITH_SUM, numOps, expprod_dd);
	    temp = operateMany(context, temp, DD.ARITH_MINUS, numOps, expprod_dd2);
	    int res = operateMany(context, temp, DD.ARITH_SUM, numOps, expprod_dd2);
	    res = operateMany(context, res, DD.ARITH_MINUS, numOps, expprod_dd);
	    return res;
    }

    public static int makeMixedTestDD(DD context, int numOps){
	    int cprod_dd = GetCountingProdDD(context, MAX_GID,2); // GetCountingDD, GetExpDD, true/false
	    int p_dd = GetExpProdDD(context, MAX_GID,1d +8e-3); // GetCountingDD, GetExpDD, true/false
	    int p_dd2 = GetExpProdDD(context, MAX_GID,1d +3e-6); // GetCountingDD, GetExpDD, true/false
	    //int temp = operateMany(context, cprod_dd, DD.ARITH_PROD, numOps, p_dd);
	    //temp = operateMany(context, temp, DD.ARITH_PROD, numOps, p_dd2);
	    //temp = operateMany(context, temp, DD.ARITH_DIV, numOps, p_dd2);
	    int res = operateMany(context, p_dd, DD.ARITH_SUM, numOps, cprod_dd);
	    res = operateMany(context, res, DD.ARITH_MINUS, numOps, cprod_dd);
	    return res;
    }

    public static String getKind(DD context){
    	String kind = "unknown";
	    if (context instanceof Table) kind = "Table";
	    if (context instanceof ADD ) kind = "ADD";
	    if (context instanceof AADD ) {
	    	int dtkind = ((AADD) context).dataKind;
	    	switch(dtkind){
	    	case AADD.SIMPLEDOUBLE:
	    		kind = "AADD-SD";
	    		break;
	    	case AADD.DOUBLEDOUBLE:
	    		kind = "AADD-DD";
	    		break;
	    	case AADD.LOGDOUBLE:
	    		kind = "AADD-LD";
	    		break;
	    	default:
	    		kind = "AADD-Ukn";
	    	}
	    }
    	return kind;
    }
}
