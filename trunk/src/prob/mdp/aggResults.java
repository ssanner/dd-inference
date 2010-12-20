package prob.mdp;

import java.io.*;
import java.text.DecimalFormat;
import java.util.*;

// Converts racetrack diagram to a .fig file
// Use fig2dev to convert to .eps, etc...
public class aggResults {

    public static final String PREFIX = "out/";
    public static final String PREFIX_OUT = "data/";
    public static final String SUFFIX = ".txt";
    public static String[] PRECS = new String[] { "0", "0.05", "0.1", "0.15", "0.2", "0.25", "0.3" };

    // SysAdmin
	//public final static boolean SPACE_AFTER_NAME = true;
    //public static int[] SIZES = new int[] { 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16 };
    //public static String[] ALGS = new String[] { "bi_ring",  "uni_ring", "star", "indep_ring" };

    // Traffic
	public final static boolean SPACE_AFTER_NAME = false;
    public static String[] ALGS = new String[] {"traffic" };
    public static int[] SIZES = new int[] { 3, 4, 5, 6, 7, 8 };
    
	public static DecimalFormat _df = new DecimalFormat("#.##");

    public static void main(String[] args) {
	
		BufferedReader in_add  = null;
		BufferedReader in_aadd = null;
		PrintStream ps_out = null;
		try {
	    	 
			// First Generate a table for each file X size with
			// 			ADD	Tm[2]	ADD Sz[3]	AADD Tm[2]	AADD Sz[3]
			// prec=0	...		
			// prec=10	...

    		for (int alg = 0; alg < ALGS.length; alg++) {

    	    	for (int sz = 0; sz < SIZES.length; sz++) {
        			
    	    		ps_out = new PrintStream(new FileOutputStream(
    	    				PREFIX_OUT + "varprec_" + ALGS[alg] + "_" + SIZES[sz] + SUFFIX));
    	    		
    	    		for (int pr = 0; pr < PRECS.length; pr++) {
    	    			
               			String input_file = PREFIX + ALGS[alg] + 
               				(SPACE_AFTER_NAME ? "_" : "") + SIZES[sz] + "_" + PRECS[pr] + SUFFIX;
    			
               			System.out.println("Processing: " + input_file);
    	    			
               			try {
               				in_add = new BufferedReader(new FileReader(input_file + ".add"));
               				in_aadd = new BufferedReader(new FileReader(input_file + ".aadd"));
               			} catch (Exception e) {System.out.println(e); continue;}
               			ps_out.print(PRECS[pr] + "\t");
    		    		//in.readLine(); // Burn first line (for unused Table comparison)
               			String add_line = null, last_add_line = null;
               			while ((add_line = in_add.readLine()) != null)
               				last_add_line = add_line;
               			String aadd_line = null, last_aadd_line = null;
               			while ((aadd_line = in_aadd.readLine()) != null)
               				last_aadd_line = aadd_line;
    		    		String[] add_stats = last_add_line.split("\t");
    		    		String[] aadd_stats = last_aadd_line.split("\t");
    		    		// Sometimes ran simultaneous to ADD, but we know error = 0
    		    		if (PRECS[pr].equals("0")) 
    		    			aadd_stats[6] = "0";
    		    		ps_out.println(add_stats[2] + "\t" + add_stats[3] + "\t" + add_stats[6] + 
    		    				"\t" + aadd_stats[2] + "\t" + aadd_stats[3] + "\t" + aadd_stats[6]);
    		    		in_add.close();
    		    		in_aadd.close();

    	    		}
    	    		
    	    		ps_out.close();
    	    	}
    		}

	    	 
			// Next Generate a table for each file X prec with
			// 			ADD	Tm[2]	ADD Sz[3]	AADD Tm[2]	AADD Sz[3]
			// size=6	...		
			// size=7	...

    		for (int alg = 0; alg < ALGS.length; alg++) {

	    		for (int pr = 0; pr < PRECS.length; pr++) {
         			
    	    		ps_out = new PrintStream(new FileOutputStream(
    	    				PREFIX_OUT + "varsize_" + ALGS[alg] + "_" + PRECS[pr].replace('.', '_') + SUFFIX));
    	    		
    	  	    	for (int sz = 0; sz < SIZES.length; sz++) {
    	    			
               			String input_file = PREFIX + ALGS[alg] + 
               				(SPACE_AFTER_NAME ? "_" : "") + SIZES[sz] + "_" + PRECS[pr] + SUFFIX;
    			
               			System.out.println("Processing: " + input_file);
    	    			
               			try {
               				in_add = new BufferedReader(new FileReader(input_file + ".add"));
               				in_aadd = new BufferedReader(new FileReader(input_file + ".aadd"));
               			} catch (Exception e) {System.out.println(e); continue;}
               			ps_out.print(SIZES[sz] + "\t");
    		    		//in.readLine(); // Burn first line (for unused Table comparison)
               			String add_line = null, last_add_line = null;
               			while ((add_line = in_add.readLine()) != null)
               				last_add_line = add_line;
               			String aadd_line = null, last_aadd_line = null;
               			while ((aadd_line = in_aadd.readLine()) != null)
               				last_aadd_line = aadd_line;
    		    		String[] add_stats = last_add_line.split("\t");
    		    		String[] aadd_stats = last_aadd_line.split("\t");
    		    		// Sometimes ran simultaneous to ADD, but we know error = 0
    		    		if (PRECS[pr].equals("0")) 
    		    			aadd_stats[6] = "0";
    		    		ps_out.println(add_stats[2] + "\t" + add_stats[3] + "\t" + add_stats[6] + 
    		    				"\t" + aadd_stats[2] + "\t" + aadd_stats[3] + "\t" + aadd_stats[6]);
    		    		in_add.close();
    		    		in_aadd.close();

    	  	    	}
    	    		
    	    		ps_out.close();
    	    	}
    		}

		
		}
		catch (Exception ignore) {
		    System.out.println("ERROR: " + ignore);
		    ignore.printStackTrace();
		    System.exit(1);
		}
	}
    	
}
