//////////////////////////////////////////////////////////////////////
//
// File:     BNTest.java 
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
// Requires: comshell package
//
// Description:
// ------------
//   Runs random queries (1 query, 1 evidence) given input parameters.
//
//////////////////////////////////////////////////////////////////////

// Package definition
package prob.bn;

// Packages to import
import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

// For greedy tree-width computations
import graph.*;

// For DD & FRB interface
import logic.add.*;

// For parsing bif files
import prob.bn.parser.*;

/**
 * Main MDP inference class
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class BNTest
{
    
    public static void main(String args[]) {
	
	if (args.length < 6 || args.length > 7) {
	    System.out.println("\nMust enter: filename, random_seed, {Table|ADD|AADD}, iter, " + 
			       "prune-prec, type<none,low,high,min,max,avg,range> [max-TW]\n");
	    System.exit(1);
	}

	// Parse problem filename
	String filename = args[0];
	int dd_type = -1;
	String ddt = args[2];
	if (ddt.equalsIgnoreCase("ADD")) {
	    dd_type = DD.TYPE_ADD;
	} else if (ddt.equalsIgnoreCase("AADD")) {
	    dd_type = DD.TYPE_AADD;
	} else if (ddt.equalsIgnoreCase("TABLE")) {
	    dd_type = DD.TYPE_TABLE;
	} else {
	    System.out.println("\nIllegal dd_type: " + ddt);
	    System.exit(1);
	}	

	// Parse prune precision and type
	int prune_type = -1;
	double prune_prec = -1d;
	int random_seed = -1;
	int iter = -1;
	int max_tw = -1;
	try {
	    random_seed = Integer.parseInt(args[1]);
	    iter = Integer.parseInt(args[3]);
	    prune_prec = (new BigDecimal(args[4])).doubleValue();
	    if (args.length > 6) {
		max_tw = Integer.parseInt(args[6]);
	    }
	} catch (NumberFormatException nfe) {
	    System.out.println("\nIllegal precision specification\n");
	    System.exit(1);
	}
	if (args[5].equalsIgnoreCase("none")) {
	    prune_type = ADD.NO_REPLACE;
	} else if (args[5].equalsIgnoreCase("low")) {
	    prune_type = ADD.REPLACE_LOW;	    
	} else if (args[5].equalsIgnoreCase("high")) {
	    prune_type = ADD.REPLACE_HIGH;
	} else if (args[5].equalsIgnoreCase("min")) {
	    prune_type = ADD.REPLACE_MIN;	    
	} else if (args[5].equalsIgnoreCase("max")) {
	    prune_type = ADD.REPLACE_MAX;
	} else if (args[5].equalsIgnoreCase("avg")) {
	    prune_type = ADD.REPLACE_AVG;
	} else if (args[5].equalsIgnoreCase("range")) {
	    prune_type = ADD.REPLACE_RANGE;
	} else {
	    System.out.println("\nIllegal prune type");
	    System.exit(1);
	}
	
	// Set up FBR for all operations
	FBR.SetPruneInfo(prune_type, prune_prec);
	BN.SetDDType(dd_type);
	Random r = new Random((long)random_seed);

	// Now generate queries
	GenQueries(filename, iter, (long)random_seed, max_tw);
    }
    
    // Runs random queries (1 query, 1 evidence) given input parameters.
    public static void GenQueries(String filename, int iter, long seed, int max_tw) {
	
	Random r = new Random(seed);
	BN bn = new BN(filename);
	
	System.out.println("\n\n");

	ArrayList vars = bn.getVariables();
	int var_sz = vars.size();

	long total_time = 0;

	// Generate a query on every iteration
	for (int i = 0; i < iter; i++) {
	    HashSet query_var  = new HashSet();
	    HashMap assignment = new HashMap();

	    // Gen query var
	    int query_var_id = r.nextInt(var_sz);
	    String qvar = (String)vars.get(query_var_id);
	    query_var.add(qvar);

	    // Gen assignment
	    int assign_var_id = r.nextInt(var_sz);
	    String avar = (String)vars.get(assign_var_id);
	    ArrayList assignments = bn.getValues(avar);
	    int assign_val_id = r.nextInt(assignments.size());
	    String aval = (String)assignments.get(assign_val_id);
	    assignment.put(avar, aval);

	    // Run query
	    if (max_tw >= 0) {
		int tw = ((Integer)bn.query(query_var, assignment, false)).intValue();
		if (tw > max_tw) {
		    System.out.println("Skipping query: " + tw);
		    --i; // Repeat iteration
		    continue;
		}
	    }
	    DD.ResetTimer();
	    System.out.println("Running query: " + query_var + " | " + assignment + " ->");
	    Object cpt = bn.query(query_var, assignment);
	    long time = DD.GetElapsedTime();
	    total_time += time;
	    System.out.println("--> Query time " + time + " ms ");
	}

	// Print out total time
	System.out.println("\nTotal time <" + filename + ", " + iter + ", " + seed + ", " + 
			   (BN.DD_TYPE == DD.TYPE_TABLE ? "Table" :
			    (BN.DD_TYPE == DD.TYPE_ADD ? "ADD" :
			     (BN.DD_TYPE == DD.TYPE_AADD ? "AADD" : "Unknown"))) +
			   ">:   " + total_time + " ms");
    }
}
