//////////////////////////////////////////////////////////////////////
//
// File:     PShell.java
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     6/7/2004
// Requires: comshell package
//
// Description:
// ------------
//   A shell interface to the prob package.  Currently only
//   handles Bayes nets, MDPs should be handled from the command
//   line interface of prob.mdp.MDP.
//
// TODO:
// -----
//   - Should really verify on a few test cases.
//   - Put this in bn subdirectory (since only for Bayes nets).
//   - Make an MDP shell for other directory.
//   - Should have two commands:
//     - load filename dd_type prune_type prune_precision
//     - query "P( Q1 ... Qm | E1=V1 ... En=Vn )"
//
//////////////////////////////////////////////////////////////////////

// Package definition
package prob;

// Packages to import
import comshell.*;
import java.io.*;
import java.text.*;
import java.util.*;
import logic.add.*;
import prob.bn.*;

/**
 * Text shell interface for a probabilistic inference system
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class PShell
{
    /* Static constants */
    public final static int    MAX_INPUT          = 4096;
    public final static String DEFAULT_PREFS_FILE = "prefs.txt";
    public final static int    INDENT             = 3;

    /* Static members */
    public static DecimalFormat _df = new DecimalFormat("0.000");

    /* Encapsulated Objects */
    public CommandInterface _ci;
    public InputStream      _is;
    public PrintStream      _os;
    public long             _lStartTime;

    /* Bayes net */
    public BN _bn;

    /* Class-defined commands */
    public int QUIT;
    public int COMMENT;
    public int TIMER;
    public int LOAD_BN;
    public int QUERY_BN;

    /** Initializes the shell interface and invokes it
     **/
    public static void main(String args[]) 
    {
	try {

	    InputStream in;
	    if (args.length >= 1)
		in = new FileInputStream(args[0]);
	    else
		in  = System.in;
		
	    PShell shell = new PShell(in, System.out);
	    shell.run();

	} catch (FileNotFoundException e) 
	    {
		System.out.println("File IO Error while reading " + args[0] + ", exiting...");
		System.exit(1);
	    }
	
    } 
    
    /** Empty constructor - uses System input/output stream and default
     *  preferences file.
     **/
    public PShell()
    {
	this(System.in, System.out, DEFAULT_PREFS_FILE);
    }

    /** Constructor - uses default preferences file.
     *  @param is InputStream to read input from
     *  @param os OutputStream to write output to
     **/
    public PShell(InputStream is, PrintStream os)
    {
	this(is, os, DEFAULT_PREFS_FILE);
    }

    /** Constructor
     *  @param is InputStream to read input from
     *  @param os OutputStream to write output to
     *  @param prefs_file File to load default environmental variable
     *                    bindings/preferences from
     **/
    public PShell(InputStream is, PrintStream os, String prefs_file)
    {
	_is     = is;
	_os     = os;
	_ci     = new CommandInterface(_is, _os);
	_bn     = null;

	// Initialize a set of commands
	TIMER         = _ci.command.addCommand("timer",
					       " {start|stop}                  - start or stop timer");
	QUIT          = _ci.command.addCommand("quit", 
					       "                                - quit application");
	COMMENT       = _ci.command.addCommand("//", 
					       "                                  - comment\n");
	LOAD_BN       = _ci.command.addCommand("load",
					       " [filename]                     - load a bayes net file");
	QUERY_BN      = _ci.command.addCommand("query",
					       "                               - query bn with env settings");
	
	// Initialize environmental variable bindings from preferences file
	_ci.initEnvVarsFromFile(prefs_file);

	// Initialize time
	_lStartTime = 0L;

	// Initialize the domain
	//_os.println("\nCreated new default kb '" + _kb + "'...");
    }
    
    /** Main command line handler
     **/
    public void run()
    {
      
	while (_ci.command.type != QUIT) {

	    try {
		_ci.getCommand();
	    } catch (IOException e) {
		_os.println("IO Error: " + e);
		while (true);
	    }
		
	    /***********************************************************
	     * Command: Quit
	     ***********************************************************/
	    if (_ci.command.type == QUIT) {
		_os.println("\nExiting PShell\n");		
	    }

	    /***********************************************************
	     * Command: Handle timer commands
	     ***********************************************************/
	    else if (_ci.command.type == TIMER) {

		if (_ci.command.numParams() != 1) {
		    _os.println("\nNeed to specify either 'start' or 'stop'.");
		} else {
		    String com = _ci.command.getParam(0);
		    if (com.equalsIgnoreCase("start")) {
			_lStartTime = System.currentTimeMillis();
		    } else if (com.equalsIgnoreCase("stop")) {
			_os.println("\nElapsed time: " + (System.currentTimeMillis() - 
							  _lStartTime) + " ms");
		    } else {
			_os.println("\nUnrecognized timer command");
		    }
		}
	    }
	    /***********************************************************
	     * Command: Handle load command
	     ***********************************************************/
	    else if (_ci.command.type == LOAD_BN) {

		if (_ci.command.numParams() > 2) {
		    _os.println("\nOnly need to specify optional filename.");
		} else {
		    String filename = null;
		    if (_ci.command.numParams() == 1) {
			filename = _ci.command.getParam(0);
		    } else {
			filename = _ci.getBindings("BN_FILENAME");			
		    }
		    _os.println("\nLoading '" + filename + "'...");

		    // Parse prune precision and type
		    String ddt = _ci.getBindings("DD_TYPE");
		    int dd_type = -1;
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
		    String pt  = _ci.getBindings("PRUNE_TYPE");
		    String pp  = _ci.getBindings("PRUNE_PREC");
		    int prune_type = -1;
		    double prune_prec = -1d;
		    try {
			prune_prec = (new Double(pp)).doubleValue();
		    } catch (NumberFormatException nfe) {
			System.out.println("\nIllegal precision specification\n");
			System.exit(1);
		    }
		    if (pt.equalsIgnoreCase("none")) {
			prune_type = ADD.NO_REPLACE;
		    } else if (pt.equalsIgnoreCase("low")) {
			prune_type = ADD.REPLACE_LOW;	    
		    } else if (pt.equalsIgnoreCase("high")) {
			prune_type = ADD.REPLACE_HIGH;
		    } else if (pt.equalsIgnoreCase("min")) {
			prune_type = ADD.REPLACE_MIN;	    
		    } else if (pt.equalsIgnoreCase("max")) {
			prune_type = ADD.REPLACE_MAX;
		    } else if (pt.equalsIgnoreCase("avg")) {
			prune_type = ADD.REPLACE_AVG;
		    } else if (pt.equalsIgnoreCase("range")) {
			prune_type = ADD.REPLACE_RANGE;
		    } else {
			System.out.println("\nIllegal prune type: '" + pt + "'");
			System.exit(1);
		    }
	
		    // Static FBR and BN setup
		    FBR.SetPruneInfo(prune_type, prune_prec);
		    BN.SetDDType(dd_type);

		    // Load the Bayes net
		    _bn = new BN(filename);
		}
	    }
	    /***********************************************************
	     * Command: Handle query command
	     ***********************************************************/
	    else if (_ci.command.type == QUERY_BN) {

		if (_ci.command.numParams() != 0) {
		    _os.println("\nNo parameters needed.");
		} else {

		    // Parse all of the variables (query and assigned)
		    HashSet query_var  = new HashSet();
		    HashMap assign_var = new HashMap();

		    Iterator entry_iter = _ci.bindings.entrySet().iterator();
		    while (entry_iter.hasNext()) {
			Map.Entry me = (Map.Entry)entry_iter.next();
			String var   = (String)me.getKey();
			String value = (String)me.getValue();
			//System.out.println(var + " --> " + value);
			if (value.startsWith("query")) {
			    query_var.add(var);
			} else if (value.startsWith("assign:")) {
			    assign_var.put(var, value.substring(7).trim().toUpperCase());
			} 
		    }
		    
		    // Run the query and print the results
		    DD.ResetTimer();
		    //int tw = ((Integer)_bn.query(query_var, assign_var, /* do_calc */ false)).intValue();
		    Object cpt = _bn.query(query_var, assign_var, /* do calc */ true);
		    //System.out.println("\nResults for query:" + query_var + ", " + assign_var);
		    //System.out.println("\nCPT:\n" + _bn._context.printNode(cpt) + "\n");
		    printProbTable(query_var, assign_var, cpt);
		    System.out.println("\nTime: " + DD.GetElapsedTime() + " ms, Size: " + _bn._context.countExactNodes(cpt) /* + " nodes, TW: " + tw*/);
		}
	    }
		
	    /***********************************************************
	     * Command: Comment '//'
	     ***********************************************************/
	    if (_ci.command.type == COMMENT) {
		; // Do nothing
	    }
		
	}
    }

    /************************************************
     * Helper functions to print probablity tables
     ************************************************/
    public void printProbTable(HashSet query_var, HashMap assign_var, Object cpt) {
	if (DD.PRUNE_TYPE == DD.REPLACE_RANGE) {
	    System.out.println("Range cpt printing not implemented");
	    System.exit(1);
	}
	System.out.print("Given evidence: [");
	StringBuffer sb = new StringBuffer();
	Iterator i = assign_var.entrySet().iterator();
	while (i.hasNext()) {
	    Map.Entry me = (Map.Entry)i.next();
	    String var = (String)me.getKey();
	    String setting = (String)me.getValue();
	    sb.append(var + "=" + setting + " ");
	}
	sb.append("]");
	System.out.println(sb.toString().toLowerCase());
	printProbEntries(new HashMap(), new LinkedList(query_var), assign_var, cpt);
    }

    public void printProbEntries(HashMap query_assigned, LinkedList query_left, 
				 HashMap assign_var, Object cpt) {
	
	if (query_left.isEmpty()) {

	    // Generate output
	    System.out.print("   - " + _df.format(_bn._context.evaluate(cpt, 
			      _bn.assign2EvalSetting(query_assigned))) + ": P( ");
	    StringBuffer sb = new StringBuffer();
	    Iterator i = query_assigned.entrySet().iterator();
	    while (i.hasNext()) {
		Map.Entry me = (Map.Entry)i.next();
		String var = (String)me.getKey();
		String setting = (String)me.getValue();
		sb.append(var + "=" + setting + " ");
	    }
	    sb.append("| evidence ");
	    sb.append(")");
	    System.out.println(sb.toString().toLowerCase());
	    return;
	    
	} else {
	    
	    // Get next var and recurse for all values
	    String var = (String)query_left.removeFirst();
	    ArrayList values = _bn.getValues(var);
	    Iterator j = values.iterator();
	    while (j.hasNext()) {
		String val = (String)j.next();
		query_assigned.put(var, val);

		// Recurse
		printProbEntries(query_assigned, query_left,
				 assign_var, cpt);

		query_assigned.remove(var);
	    }

	    // Now reset so that parent can recurse on other values
	    query_left.addFirst(var);
	    return;
	}
    }
}







