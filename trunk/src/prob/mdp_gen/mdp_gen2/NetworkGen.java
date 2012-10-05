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
package prob.mdp_gen;

// Packages to import
import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;
import logic.add_gen.*;

/**
 * Generates network problems from a HashMap of ID's and connections
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class NetworkGen
{
    public static boolean PERTURB_REWARD = false;
    
    /** Static configurations **/
    public static HashMap INDEX          = new HashMap();

    public static HashMap STAR_6         = new HashMap();
    public static HashMap STAR_7         = new HashMap();
    public static HashMap STAR_8         = new HashMap();
    public static HashMap STAR_9         = new HashMap();
    public static HashMap STAR_10        = new HashMap();
    public static HashMap STAR_11        = new HashMap();
    public static HashMap STAR_12        = new HashMap();
    public static HashMap STAR_13        = new HashMap();
    public static HashMap STAR_14        = new HashMap();
    public static HashMap STAR_15        = new HashMap();
    public static HashMap STAR_16        = new HashMap();

    public static final int MAX_RING = 16;
    public static HashMap[] UNI_RING     = new HashMap[MAX_RING+1];
    public static HashMap[] BI_RING      = new HashMap[MAX_RING+1];
    public static HashMap[] INDEP_RING   = new HashMap[MAX_RING+1];

    public static HashMap INDEP_RING3_6   = new HashMap(); 
    public static HashMap INDEP_RING4_8   = new HashMap(); 
    public static HashMap INDEP_RING5_10  = new HashMap(); 

    public static HashMap INDEP_RING_EPS_6  = new HashMap();
    public static HashMap INDEP_RING_EPS_8  = new HashMap();
    public static HashMap INDEP_RING_EPS_10 = new HashMap();

    static {
	int i;
	for (i = 0; i <= MAX_RING; i++) {
	    UNI_RING[i] = new HashMap();
	    GenUniRing(UNI_RING[i], i);
	    INDEX.put("uni_ring_" + i, UNI_RING[i]);
	}
	for (i = 0; i <= MAX_RING; i++) {
	    BI_RING[i] = new HashMap();
	    GenBiRing(BI_RING[i], i);
	    INDEX.put("bi_ring_" + i, BI_RING[i]);
	}
	for (i = 0; i <= MAX_RING; i++) {
	    INDEP_RING[i] = new HashMap();
	    GenIndepRing(INDEP_RING[i], i);
	    INDEX.put("indep_ring_" + i, INDEP_RING[i]);
	}
    }

    public static void GenUniRing(HashMap h, int n) {
	for (int i = 1; i < n; i++) {
	    AddConn(h, i, i+1);
	}
	AddConn(h,n,1);
    }

    public static void GenBiRing(HashMap h, int n) {
	for (int i = 1; i < n; i++) {
	    AddConn(h, i, i+1);
	}
	AddConn(h,n,1);
	for (int j = n; j > 1; j--) {
	    AddConn(h, j, j-1);
	}
	AddConn(h,1,n);
    }

    public static void GenIndepRing(HashMap h, int n) {
	for (int i = 1; i < n; i+=2) {
	    AddConn(h, i, i+1);
	    AddConn(h, i+1, i);
	}
	if ((n & 1) == 1) {
	    // Odd
	    AddConn(h,n,n);
	}
    }

    /** For printing **/
    public static DecimalFormat _df = new DecimalFormat("#.####");

    /** Generator **/
    public static void GenNetworkFile(String filename, HashMap config) {
	
	PrintWriter os = null;
	try {
	    // Open the output file
	    os = new PrintWriter(new FileOutputStream(filename));
	    
	    // Get all ids and print them to the file
	    TreeSet ids_tmp = new TreeSet(config.keySet());
	    TreeSet ids = new TreeSet();
	    Iterator it = ids_tmp.iterator();
	    while (it.hasNext()) {
		int c_id = ((Integer)it.next()).intValue();
		if (c_id > 0) {
		    ids.add(new Integer(c_id));
		}
	    }
	    Integer id1 = null, id2 = null;
	    Iterator i = ((Set)ids.clone()).iterator();
	    while (i.hasNext()) {
		ids.addAll((Set)config.get(i.next()));
	    }
	    os.print("variables (");
	    i = ids.iterator();
	    while (i.hasNext()) {
		os.print("c" + i.next() + " ");
	    }
	    os.println(")");

	    // Generate order and ADD
	    ArrayList order = new ArrayList(ids);
	    ADD context = new ADD(order);
	    
	    // Generate generic noreboot
	    os.println("action noreboot");
	    System.out.println("\nAction: noreboot");
	    Iterator i2 = ids.iterator();
	    while (i2.hasNext()) {
		id2 = (Integer)i2.next();
			
		// Not being rebooted
		TreeSet ts = GetIncomingConn(id2, config);
		System.out.println(id2 + " <-- " + ts);
		
		// Here need to generate positive side of CPT
		// where dependent upon current computer's 
		// status and scaled by conn computer's status.
		// TODO: (Work this out.)
		int id = GetCountingDD(context, ts, 1d, false);
		int conn = context.scalarMultiply( id, 1.0d/((double)ts.size() + 1.0d) );
		int conn_t = context.scalarMultiply(conn, 0.95d);
		int conn_f = context.scalarMultiply(conn, 0.0475d);

		TreeSet tse = GetIncomingEpsConn(id2, config);
		if (!tse.isEmpty()) {
		    System.out.println(id2 + " <-- " + tse + " [EPS]");
		    int conne = GetCountingDD(context, tse, 1d, false);
		    conne = context.scalarMultiply(conne, 0.001d);
		    conn_t = context.applyInt(conn_t, conne, ADD.ARITH_MINUS);
		    conn_f = context.applyInt(conn_f, conne, ADD.ARITH_MINUS);
		}
		
		os.print("\tc" + id2 + " (c" + id2 + " ");
		context.dumpToTree(conn_t, "c", os, _df, 4);
		context.dumpToTree(conn_f, "c", os, _df, 4);
		os.println(") ");
	    }
	    os.println("endaction");
	    
	    // Now, generate all actions
	    i = ids.iterator();
	    while (i.hasNext()) {
		id1 = (Integer)i.next();
		os.println("action reboot" + id1);
		System.out.println("\nAction: reboot" + id1);
		i2 = ids.iterator();
		while (i2.hasNext()) {
		    id2 = (Integer)i2.next();
		    
		    if (id1.equals(id2)) {
			
			// Is being rebooted?
			os.println("\tc" + id2 + " (1.00)");
			System.out.println(id2 + " <-- <reboot>");
			
		    } else {
			
			// Not being rebooted
			TreeSet ts = GetIncomingConn(id2, config);
			System.out.println(id2 + " <-- " + ts);

			// Here need to generate positive side of CPT
			// where dependent upon current computer's 
			// status and scaled by conn computer's status.
			// TODO: (Work this out.)
			int id = GetCountingDD(context, ts, 1d, false);
			int conn = context.scalarMultiply( id, 1.0d/((double)ts.size() + 1.0d) );
			int conn_t = context.scalarMultiply(conn, 0.95d);
			int conn_f = context.scalarMultiply(conn, 0.0475d);

			TreeSet tse = GetIncomingEpsConn(id2, config);
			if (!tse.isEmpty()) {
			    System.out.println(id2 + " <-- " + tse + " [EPS]");
			    int conne = GetCountingDD(context, tse, 1d, false);
			    conne = context.scalarMultiply(conne, 0.001d);
			    conn_t = context.applyInt(conn_t, conne, DD.ARITH_MINUS);
			    conn_f = context.applyInt(conn_f, conne, DD.ARITH_MINUS);
			}
			
			os.print("\tc" + id2 + " (c" + id2 + " ");
			context.dumpToTree(conn_t, "c", os, _df, 4);
			context.dumpToTree(conn_f, "c", os, _df, 4);
			os.println(") ");
			
		    }
		}
		os.println("endaction");
	    }

	    // Now generate reward
	    os.print("reward ");
	    int rew = GetCountingDD(context, ids, 0d, PERTURB_REWARD);
	    context.dumpToTree(rew, "c", os, _df, 0);

	    // Generate discount and tolerance
	    os.println("\n\ndiscount 0.900000");
	    os.println("tolerance 0.010000");

	    // Close file
	    os.close();

	} catch (IOException ioe) { System.out.println(ioe); System.exit(1); }
    }

    // Returns a counting ADD from gid 1..max_gid
    public static int GetCountingDD(DD context, Set vars, double off, boolean perturb) {
	//System.out.println("GETCD: " + vars + ", " + context._alOrder);
	int ret = context.getConstantNode(off);
	Iterator i = vars.iterator();
	while (i.hasNext()) {
	    int var = ((Integer)i.next()).intValue();
	    ret = context.applyInt(ret, context.getVarNode(var, 0d, perturb ? 1e-4d * var + 1d : 1d), DD.ARITH_SUM);
	}
	return ret;
    }

    public static TreeSet GetIncomingConn(Integer id, HashMap config) {
	TreeSet ret = new TreeSet();
	Iterator i = config.keySet().iterator();
	while (i.hasNext()) {
	    Integer id2 = (Integer)i.next();
	    if (id2.intValue() < 0) {
		continue;
	    }
	    TreeSet t   = (TreeSet)config.get(id2);
	    if (t != null && t.contains(id)) {
		ret.add(id2);
	    }
	}
	return ret;
    }

    public static TreeSet GetIncomingEpsConn(Integer id, HashMap config) {
	Integer nid = new Integer(-id.intValue());
	TreeSet ret = new TreeSet();
	Iterator i = config.keySet().iterator();
	while (i.hasNext()) {
	    Integer id2 = (Integer)i.next();
	    if (id2.intValue() > 0) {
		continue;
	    }
	    TreeSet t   = (TreeSet)config.get(id2);
	    if (t != null && t.contains(nid)) {
		ret.add(new Integer(-id2.intValue()));
	    }
	}
	return ret;
    }

    /** Main **/
    public static void main(String[] args) {
	if (args.length != 1) {
	    System.out.println("java prob.mdp.NetworkGen <perturb-reward=true/false>");
	    System.exit(1);
	} else if (args[0].equalsIgnoreCase("true")) {
	    PERTURB_REWARD = true;
	} else if (args[0].equalsIgnoreCase("false")) {
	    PERTURB_REWARD = false;
	} else {
	    System.out.println("java prob.mdp.NetworkGen perturb-reward=true/false");
	    System.exit(1);
	}
	Iterator i = INDEX.entrySet().iterator();
	while (i.hasNext()) {
	    Map.Entry me   = (Map.Entry)i.next();
	    String name    = ((String)me.getKey()) + ".net";
	    HashMap config = (HashMap)me.getValue();
	    System.out.println("Generating '" + name + "' from configuration.");
	    GenNetworkFile(name, config);
	}
    }

    /** Network building methods **/
    public static void AddConn(HashMap map, int from, int to) {
	Integer FROM = new Integer(from);
	Integer TO   = new Integer(to);
	TreeSet ts = (TreeSet)map.get(FROM);
	if (ts == null) {
	    ts = new TreeSet();
	    map.put(FROM, ts);
	}
	ts.add(TO);
    }

    static {
	INDEX.put("star_6",  STAR_6);
	INDEX.put("star_7",  STAR_7);
	INDEX.put("star_8",  STAR_8);
	INDEX.put("star_9",  STAR_9);
	INDEX.put("star_10", STAR_10);
	INDEX.put("star_11", STAR_11);
	INDEX.put("star_12", STAR_12);
	INDEX.put("star_13", STAR_13);
	INDEX.put("star_14", STAR_14);
	INDEX.put("star_15", STAR_15);
	INDEX.put("star_16", STAR_16);

	INDEX.put("indep_ring3_6", INDEP_RING3_6);
	INDEX.put("indep_ring4_8", INDEP_RING4_8);
	INDEX.put("indep_ring5_10", INDEP_RING5_10);

	INDEX.put("indep_ring_eps_6", INDEP_RING_EPS_6);
	INDEX.put("indep_ring_eps_8", INDEP_RING_EPS_8);
	INDEX.put("indep_ring_eps_10", INDEP_RING_EPS_10);
    }

    /** STAR 6 **/
    static {
	AddConn(STAR_6,4,1);
	AddConn(STAR_6,5,2);
	AddConn(STAR_6,5,3);
	AddConn(STAR_6,6,4);
	AddConn(STAR_6,6,5);
    }

    /** STAR 7 **/
    static {
	AddConn(STAR_7,5,1);
	AddConn(STAR_7,5,2);
	AddConn(STAR_7,6,3);
	AddConn(STAR_7,6,4);
	AddConn(STAR_7,7,5);
	AddConn(STAR_7,7,6);
    }

    /** STAR 8 **/
    static {
	AddConn(STAR_8,5,1);
	AddConn(STAR_8,5,2);
	AddConn(STAR_8,6,3);
	AddConn(STAR_8,7,4);
	AddConn(STAR_8,8,5);
	AddConn(STAR_8,8,6);
	AddConn(STAR_8,8,7);
    }

    /** STAR 9 **/
    static {
	AddConn(STAR_9,6,1);
	AddConn(STAR_9,6,2);
	AddConn(STAR_9,7,3);
	AddConn(STAR_9,7,4);
	AddConn(STAR_9,8,5);
	AddConn(STAR_9,9,6);
	AddConn(STAR_9,9,7);
	AddConn(STAR_9,9,8);
    }

    /** STAR 10 **/
    static {
	AddConn(STAR_10,7,1);
	AddConn(STAR_10,7,2);
	AddConn(STAR_10,8,3);
	AddConn(STAR_10,8,4);
	AddConn(STAR_10,9,5);
	AddConn(STAR_10,9,6);
	AddConn(STAR_10,10,7);
	AddConn(STAR_10,10,8);
	AddConn(STAR_10,10,9);
    }

    /** STAR 11 **/
    static {
	AddConn(STAR_11,8,1);
	AddConn(STAR_11,8,2);
	AddConn(STAR_11,9,3);
	AddConn(STAR_11,9,4);
	AddConn(STAR_11,10,5);
	AddConn(STAR_11,10,6);
	AddConn(STAR_11,10,7);
	AddConn(STAR_11,11,8);
	AddConn(STAR_11,11,9);
	AddConn(STAR_11,11,10);
    }

    /** STAR 12 **/
    static {
	AddConn(STAR_12,9,1);
	AddConn(STAR_12,9,2);
	AddConn(STAR_12,10,3);
	AddConn(STAR_12,10,4);
	AddConn(STAR_12,10,5);
	AddConn(STAR_12,11,6);
	AddConn(STAR_12,11,7);
	AddConn(STAR_12,11,8);
	AddConn(STAR_12,12,9);
	AddConn(STAR_12,12,10);
	AddConn(STAR_12,12,11);
    }

    /** STAR 13 **/
    static {
	AddConn(STAR_13,10,1);
	AddConn(STAR_13,10,2);
	AddConn(STAR_13,10,3);
	AddConn(STAR_13,11,4);
	AddConn(STAR_13,11,5);
	AddConn(STAR_13,11,6);
	AddConn(STAR_13,12,7);
	AddConn(STAR_13,12,8);
	AddConn(STAR_13,12,9);
	AddConn(STAR_13,13,10);
	AddConn(STAR_13,13,11);
	AddConn(STAR_13,13,12);
    }

    /** STAR 14 **/
    static {
	AddConn(STAR_14,10,1);
	AddConn(STAR_14,10,2);
	AddConn(STAR_14,10,3);
	AddConn(STAR_14,11,4);
	AddConn(STAR_14,11,5);
	AddConn(STAR_14,11,6);
	AddConn(STAR_14,12,7);
	AddConn(STAR_14,12,8);
	AddConn(STAR_14,13,9);
	AddConn(STAR_14,14,10);
	AddConn(STAR_14,14,11);
	AddConn(STAR_14,14,12);
	AddConn(STAR_14,14,13);
    }

    /** STAR 15 **/
    static {
	AddConn(STAR_15,11,1);
	AddConn(STAR_15,11,2);
	AddConn(STAR_15,11,3);
	AddConn(STAR_15,12,4);
	AddConn(STAR_15,12,5);
	AddConn(STAR_15,12,6);
	AddConn(STAR_15,13,7);
	AddConn(STAR_15,13,8);
	AddConn(STAR_15,14,9);
	AddConn(STAR_15,14,10);
	AddConn(STAR_15,15,11);
	AddConn(STAR_15,15,12);
	AddConn(STAR_15,15,13);
	AddConn(STAR_15,15,14);
    }

    /** STAR 16 **/
    static {
	AddConn(STAR_13,12,1);
	AddConn(STAR_13,12,2);
	AddConn(STAR_13,12,3);
	AddConn(STAR_13,13,4);
	AddConn(STAR_13,13,5);
	AddConn(STAR_13,13,6);
	AddConn(STAR_13,14,7);
	AddConn(STAR_13,14,8);
	AddConn(STAR_13,14,9);
	AddConn(STAR_13,15,10);
	AddConn(STAR_13,15,11);
	AddConn(STAR_13,16,12);
	AddConn(STAR_13,16,13);
	AddConn(STAR_13,16,14);
	AddConn(STAR_13,16,15);
    }

    /** INDEPENDENT RING 2x3 (6 total) **/
    static {
	AddConn(INDEP_RING3_6,1,2);
	AddConn(INDEP_RING3_6,2,3);
	AddConn(INDEP_RING3_6,3,1);

	AddConn(INDEP_RING3_6,4,5);
	AddConn(INDEP_RING3_6,5,6);
	AddConn(INDEP_RING3_6,6,4);
    }

    /** INDEPENDENT RING 2x4 (8 total) **/
    static {
	AddConn(INDEP_RING4_8,1,2);
	AddConn(INDEP_RING4_8,2,3);
	AddConn(INDEP_RING4_8,3,4);
	AddConn(INDEP_RING4_8,4,1);

	AddConn(INDEP_RING4_8,5,6);
	AddConn(INDEP_RING4_8,6,7);
	AddConn(INDEP_RING4_8,7,8);
	AddConn(INDEP_RING4_8,8,5);
    }

    /** INDEPENDENT RING 2x5 (10 total) **/
    static {
	AddConn(INDEP_RING5_10,1,2);
	AddConn(INDEP_RING5_10,2,3);
	AddConn(INDEP_RING5_10,3,4);
	AddConn(INDEP_RING5_10,4,5);
	AddConn(INDEP_RING5_10,5,1);

	AddConn(INDEP_RING5_10,6,7);
	AddConn(INDEP_RING5_10,7,8);
	AddConn(INDEP_RING5_10,8,9);
	AddConn(INDEP_RING5_10,9,10);
	AddConn(INDEP_RING5_10,10,6);
    }

    /** INDEPENDENT RING 6 EPS **/
    static {
	AddConn(INDEP_RING_EPS_6,1,2);
	AddConn(INDEP_RING_EPS_6,2,1);
	AddConn(INDEP_RING_EPS_6,-3,-2); // eps conn

	AddConn(INDEP_RING_EPS_6,3,4);
	AddConn(INDEP_RING_EPS_6,4,3);
	AddConn(INDEP_RING_EPS_6,-5,-4); // eps conn

	AddConn(INDEP_RING_EPS_6,5,6);
	AddConn(INDEP_RING_EPS_6,6,5);
	AddConn(INDEP_RING_EPS_6,-1,-6); // eps conn
    }

    /** INDEPENDENT RING 8 EPS **/
    static {
	AddConn(INDEP_RING_EPS_8,1,2);
	AddConn(INDEP_RING_EPS_8,2,1);
	AddConn(INDEP_RING_EPS_8,-3,-2); // eps conn

	AddConn(INDEP_RING_EPS_8,3,4);
	AddConn(INDEP_RING_EPS_8,4,3);
	AddConn(INDEP_RING_EPS_8,-5,-4); // eps conn

	AddConn(INDEP_RING_EPS_8,5,6);
	AddConn(INDEP_RING_EPS_8,6,5);
	AddConn(INDEP_RING_EPS_8,-7,-6); // eps conn

	AddConn(INDEP_RING_EPS_8,7,8);
	AddConn(INDEP_RING_EPS_8,8,7);
	AddConn(INDEP_RING_EPS_8,-1,-8); // eps conn
    }

    /** INDEPENDENT RING 10 EPS **/
    static {
	AddConn(INDEP_RING_EPS_10,1,2);
	AddConn(INDEP_RING_EPS_10,2,1);
	AddConn(INDEP_RING_EPS_10,-3,-2); // eps conn

	AddConn(INDEP_RING_EPS_10,3,4);
	AddConn(INDEP_RING_EPS_10,4,3);
	AddConn(INDEP_RING_EPS_10,-5,-4); // eps conn

	AddConn(INDEP_RING_EPS_10,5,6);
	AddConn(INDEP_RING_EPS_10,6,5);
	AddConn(INDEP_RING_EPS_10,-7,-6); // eps conn

	AddConn(INDEP_RING_EPS_10,7,8);
	AddConn(INDEP_RING_EPS_10,8,7);
	AddConn(INDEP_RING_EPS_10,-9,-8); // eps conn

	AddConn(INDEP_RING_EPS_10,9,10);
	AddConn(INDEP_RING_EPS_10,10,9);
	AddConn(INDEP_RING_EPS_10,-1,-10); // eps conn
    }
}
