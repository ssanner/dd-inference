//////////////////////////////////////////////////////////////////
//                    Testing Methods for ADD
//////////////////////////////////////////////////////////////////

package logic.add;

import java.io.*;
import java.util.*;

public class Compare {

    // Precision setting (1e-10 currently)
    public static final double PRECISION = AADD.PRECISION;
    
    // Show cache
    public static final boolean SHOW_CACHE = false;
    
    // Internal timing stats
    public static long _lTime;

    // General testing methods for the ADD class
    public static void main(String[] args) {

	// Prune?
	FBR.SetPruneInfo(DD.NO_REPLACE, -1);
	//FBR.SetPruneInfo(DD.REPLACE_LOW, 1e-10);

	// Flags: exp    prod   invert other  sq?
	/*
	// Perform SUM test 
	CompareOp(false, false, false, false, true,  14, DD.MAX_ITER, "sum_count.txt");*/
	CompareOp(true,  false, false, false, true,  14, 14, "sum_exp.txt");
	
	/*
	// Perform PROD test
	CompareOp(false, true,  false, false, true,  14, DD.MAX_ITER, "prod_count.txt");*/
	CompareOp(true,  true,  false, false, true,  14, 14, "prod_exp.txt");

	// Perform MAX test 1 - Many MAX optimizations
	/*	CompareOp(false, true,  false,  true, false, 14, DD.MAX_ITER, "max_many_count.txt");*/
	CompareOp(true,  true,  false,  true, false, 14, 14, "max_many_exp.txt");
	
	/*
	// Perform MAX test 2 - Few MAX optimizations
	CompareOp(false, true,  false,  true, true,  14, DD.MAX_ITER, "max_few_count.txt");
	CompareOp(true,  true,  false,  true, true,  14, 14, "max_few_exp.txt");
	
	// Perform OTHER test 
	// CompareOp(false, false, false,  true, true,  14, DD.MAX_ITER, "other_count.txt");
	// CompareOp(true,  false, false,  true, true,  14, 14, "other_exp.txt");

	// Perform INVERT test
	CompareOp(false, false, true,  false, true,  14, DD.MAX_ITER, "invert_count.txt");
	CompareOp(true,  false, true,  false, true,  14, 14, "invert_exp.txt");
	*/
	
	// Perform squared counting test
	CompareCountSq(14, 14, "count_square.txt");

	new ADD(new ArrayList()).pruneReport();
	new AADD(new ArrayList()).pruneReport();
    }

    // Reset the timer
    public static void ResetTimer() {
	_lTime = System.currentTimeMillis();
    }

    // Get the elapsed time since resetting the timer
    public static long GetElapsedTime() {
	return System.currentTimeMillis() - _lTime;
    }

    // Returns a counting ADD from gid 1..max_gid
    public static int GetCountingDD(DD context, int max_gid, boolean skip) {
	int ret = context.getVarNode(/*gid*/ 1, /*low*/ 0d, /*high*/ 1d);
	for (int i=2; i <= max_gid; i += (skip ? 2 : 1)) {
	    ret = context.applyInt(ret, context.getVarNode(i, 0d, 1d), DD.ARITH_SUM);
	}
	return ret;
    }

    // Returns an exponential coefficient ADD (a + 2b + 4c + ...) from 1..max_gid
    public static int GetExpDD(DD context, int max_gid, boolean skip) {
	int ret = context.getVarNode(1, 0d, 1d);
	int coef = 1;
	for (int i=2; i <= max_gid; i += (skip ? 2 : 1)) {
	    coef = coef << 1;
	    ret = context.applyInt(ret, context.getVarNode(i,0d,(double)coef), DD.ARITH_SUM);
	}
	return ret;	
    }

    // Returns a product ADD (abcd... = val) from 1..max_gid
    public static int GetCountingProdDD(DD context, int max_gid, double gamma) {
	int ret = context.getVarNode(1, 1d, Math.pow(gamma,1d));
	for (int i=2; i <= max_gid; i++) {
	    ret = context.applyInt(ret, context.getVarNode(i, 1d,
							   Math.pow(gamma, 1d)), 
				   DD.ARITH_PROD);
	}
	return ret;
    }

    // Returns a product ADD (abcd... = val) from 1..max_gid
    public static int GetExpProdDD(DD context, int max_gid, double gamma) {
	int coef = 1;
	int ret = context.getVarNode(1, 1d, Math.pow(gamma,(double)coef));
	for (int i=2; i <= max_gid; i++) {
	    coef  = coef << 1;
	    ret = context.applyInt(ret, context.getVarNode(i, 1d,
							   Math.pow(gamma, (double)coef)), 
				   DD.ARITH_PROD);
	}
	return ret;
    }

    // This tests the binary operations
    public static void CompareOp(boolean exp, boolean prod, boolean invert, boolean other, 
				 boolean square, int table_cutoff, int aadd_cutoff, String outfile) {

	PrintWriter os = null;
	if (outfile != null) {
	    try {
		os = new PrintWriter(new FileOutputStream(outfile));
	    } catch (Exception ioe) { }
	}

	System.out.println("\nPerforming " + 
			   (other ? (prod ? "*MAX* for " + (square ? "[SQ] " : ""): "*OTHER* for ") : 
			    (invert ? "*INVERSION* of " : 
			   (prod ? "*PRODUCT* of " : "*SUM* of "))) + 
			   (exp ? "*EXP* dd" : "*COUNTING* dd") + 
			   " comparison:\n-------------------------------------------------\n");

	System.out.println("#vars: Table time/nodes ADD time/nodes AADD time/nodes - max diff");
	
	for (int mvars = 6; mvars <= aadd_cutoff; mvars += 1) {

	    ArrayList order = new ArrayList();
	    for (int i = 1; i <= mvars; i++) {
		order.add(new Integer(i));
	    }

	    DD[] dd = new DD[3];
	    dd[0] = new Table(order);
	    dd[1] = new ADD(order);
	    dd[2] = new AADD(order);
	    long[] time  = new long[3];
	    long[] nodes = new long[3];
	    int[] ddr = new int[3]; ddr[0] = ddr[1] = ddr[2] = DD.INVALID;

	    System.out.print(mvars + ": ");

	    for (int dd_type = 0; dd_type <= 2; dd_type++) {
		
		if (dd_type == 0 && mvars > table_cutoff) {
		    continue;
		}

		// Perform DD test
		int dd1 = DD.INVALID, dd2 = DD.INVALID;

		if (exp) {
		    dd1 = prod 
			? GetExpProdDD(dd[dd_type], mvars, 0.9999d)
			: GetExpDD(dd[dd_type], mvars, false);
		    dd2 = prod 
			? GetExpProdDD(dd[dd_type], mvars, 0.9999d)
			: GetExpDD(dd[dd_type], mvars, false);
		    //dd2 = prod 
		    //	? dd[dd_type].scalarMultiply(dd2, 0.9d)
		    //	: dd[dd_type].scalarMultiply(dd2, 2d);
		} else {
		    dd1 = prod 
			? GetCountingProdDD(dd[dd_type], mvars, 0.999d)
			: GetCountingDD(dd[dd_type], mvars, false);
		    dd2 = prod 
			? GetCountingProdDD(dd[dd_type], mvars, 0.999d)
			: GetCountingDD(dd[dd_type], mvars, false);
		    //dd2 = prod 
		    //	? dd[dd_type].scalarMultiply(dd2, 0.9d)
		    //	: dd[dd_type].scalarMultiply(dd2, 2d);
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
			ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2, DD.ARITH_MAX);
		    } else {
			if (square) {
			    dd1 = dd[dd_type].applyInt(dd1, dd1, DD.ARITH_PROD);
			}
			dd1 = dd[dd_type].negate(dd1);
			dd1 = dd[dd_type].scalarAdd(dd1, 3d);
			ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2, prod ? DD.ARITH_PROD : DD.ARITH_SUM);
		    }
		} else if (invert) {
		    ddr[dd_type] = dd[dd_type].scalarAdd(dd1, 1.0d);
		    ddr[dd_type] = dd[dd_type].invert(ddr[dd_type]);
		} else {
		    ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2, prod ? DD.ARITH_PROD : DD.ARITH_SUM);
		}

		if (dd_type == 1 && mvars <= 5) {
		    DD.PrintEnum(dd[1], dd1);
		    DD.PrintEnum(dd[1], ddr[1]);
		}

		// Prune?
		//ddr[dd_type] = dd[dd_type].pruneNodes(ddr[dd_type]);
		time[dd_type]  = GetElapsedTime();
		nodes[dd_type] = dd[dd_type].countExactNodes(ddr[dd_type]);
		System.out.print(time[dd_type] + "/" + nodes[dd_type] + "  ");
	    }
 
	    if (mvars <= 16) {
		System.out.println("  diff: " + 
				   (mvars <= table_cutoff ? DD._df.format(DD.CompareEnum(dd[0], ddr[0], dd[1], ddr[1])) + ", " : "") + 
				   DD._df.format(DD.CompareEnum(dd[1], ddr[1], dd[2], ddr[2]))
				   + " [" + DD.RUNTIME.totalMemory() + "] ");
	    } else {
		System.out.println();
	    }

	    // Output to file?
	    if (os != null) {
		try {
		    os.println(mvars + " " + time[0] + " " + nodes[0] + " " +
			       time[1] + " " + nodes[1] + " " +
			       time[2] + " " + nodes[2]);
		} catch (Exception ioe) { }
	    }
	}
	
	if (os != null) {
	    try {
		os.close();
	    } catch (Exception ioe) { }
	}
	System.out.println();
    }

    // This tests the binary operations
    public static void CompareCountSq(int table_cutoff, int aadd_cutoff, String outfile) {

	PrintWriter os = null;
	if (outfile != null) {
	    try {
		os = new PrintWriter(new FileOutputStream(outfile));
	    } catch (Exception ioe) { }
	}

	System.out.println("\nPerforming square of counting DD comparison:\n-------------------------------------------------\n");

	System.out.println("#vars: Table time/nodes ADD time/nodes AADD time/nodes - max diff");
	
	for (int mvars = 6; mvars <= aadd_cutoff; mvars += 1) {

	    ArrayList order = new ArrayList();
	    for (int i = 1; i <= mvars; i++) {
		order.add(new Integer(i));
	    }

	    DD[] dd = new DD[3];
	    dd[0] = new Table(order);
	    dd[1] = new ADD(order);
	    dd[2] = new AADD(order);
	    long[] time  = new long[3];
	    long[] nodes = new long[3];
	    int[] ddr = new int[3]; ddr[0] = ddr[1] = ddr[2] = DD.INVALID;

	    System.out.print(mvars + ": ");

	    for (int dd_type = 0; dd_type <= 2; dd_type++) {
		
		if (dd_type == 0 && mvars > table_cutoff) {
		    continue;
		}

		// Perform DD test
		int dd1 = DD.INVALID, dd2 = DD.INVALID;

	    dd1 = GetExpDD(dd[dd_type], mvars, false);
	    dd2 = GetExpDD(dd[dd_type], mvars, false);
		    
		dd[dd_type].addSpecialNode(dd1);
		dd[dd_type].addSpecialNode(dd2);
		dd[dd_type].flushCaches(false);
		
		ResetTimer();
		ddr[dd_type] = dd[dd_type].applyInt(dd1, dd2, DD.ARITH_PROD);

		if (dd_type == 1 && mvars <= 5) {
		    DD.PrintEnum(dd[1], dd1);
		    DD.PrintEnum(dd[1], ddr[1]);
		}

		// Prune?
		//ddr[dd_type] = dd[dd_type].pruneNodes(ddr[dd_type]);
		time[dd_type]  = GetElapsedTime();
		nodes[dd_type] = dd[dd_type].countExactNodes(ddr[dd_type]);
		System.out.print(time[dd_type] + "/" + nodes[dd_type] + "  ");
	    }
 
	    if (mvars <= 16) {
		System.out.println("  diff: " + 
				   (mvars <= table_cutoff ? DD._df.format(DD.CompareEnum(dd[0], ddr[0], dd[1], ddr[1])) + ", " : "") + 
				   DD._df.format(DD.CompareEnum(dd[1], ddr[1], dd[2], ddr[2]))
				   + " [" + DD.RUNTIME.totalMemory() + "] ");
	    } else {
		System.out.println();
	    }

	    // Output to file?
	    if (os != null) {
		try {
		    os.println(mvars + " " + time[0] + " " + nodes[0] + " " +
			       time[1] + " " + nodes[1] + " " +
			       time[2] + " " + nodes[2]);
		} catch (Exception ioe) { }
	    }
	}
	
	if (os != null) {
	    try {
		os.close();
	    } catch (Exception ioe) { }
	}
	System.out.println();
    }

    
}
