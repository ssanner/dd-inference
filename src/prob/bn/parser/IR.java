//////////////////////////////////////////////////////////////////////
//
// File:     IR.java (Intermediate representation for Bayes net)
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     9/1/2003
//
// Description:
// ------------
// A structure parser for an intermediate representation of Bayes nets.
//
// TODO:
// -----
// - Files to test (carpo - noisy max & row entries, Alarm_JB - table)
// - Should also read bif output of JavaBayes, i.e. table probability.
//
//////////////////////////////////////////////////////////////////////

// Package definition
package prob.bn.parser;

// Packages to import
import java.io.*;
import java.math.*;
import java.text.*;
import java.util.*;

import graph.*;

/**
 * IR parser class
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class IR
{
    //////////////////////////////////////////////////////////////
    //                       Member Variables
    //////////////////////////////////////////////////////////////
    public    Network _network;
    protected Yylex   _lex;
    protected Symbol  _lastToken;

    //////////////////////////////////////////////////////////////
    //                     Local Classes in IR
    //////////////////////////////////////////////////////////////
    public static class Network {
	public String  _sName;
	public HashMap _hmVariables;
	public HashMap _hmCPTs;

	public Network(String s) {
	    _sName = s;
	    _hmVariables = new HashMap();
	    _hmCPTs      = new HashMap();
	}

	public int getNumValues(String var) {
	    return ((Variable)_hmVariables.get(var))._alValues.size();
	}

	public ArrayList getValues(String var) {
	    return ((Variable)_hmVariables.get(var))._alValues;
	}

	/** Converts from value labels to value IDs
	 **/
	public ArrayList values2Indices(ArrayList vars, ArrayList values) {
	    ArrayList indices = new ArrayList();
	    for (int i = 0; i < vars.size(); i++) {
		ArrayList index_list = getValues((String)vars.get(i));
		//System.out.println("Index list: " + index_list + ", vals: " + 
		//		   values.get(i));
		indices.add( new Integer( index_list.indexOf(values.get(i))) );
	    }
	    return indices;
	}

	public String toString() {
	    return "Network: " +_sName + 
		"\nVariables: " + _hmVariables + 
		"\nCPTS: " + _hmCPTs;
	}
    }

    public static class Variable {
	public String    _sName;
	public String    _sLabel;
	public ArrayList _alValues; // Values referenced as ints,
	                            // String ident given by int index

	public Variable(String s) {
	    _sName = s;
	    _alValues = new ArrayList();
	}

	public int getBinValues() {
	    return (int)Math.ceil(Math.log(_alValues.size())/Math.log(2d));
	}

	public String toString() {
	    return "[Var: '" + _sName + "', Label: '" + _sLabel + "', " +
		"', Values: " + _alValues + ", BVars: " + getBinValues() + "]";
	}
    }

    public static class CPT {
	public String    _sChild;
	public ArrayList _alParents; // All vars including head
	public String    _sFunProperty;
	public TreeMap   _tmEntries; // ArrayList of ArrayList of lines

	public CPT(String s) {
	    _sChild = s;
	    _sFunProperty = null;
	    _alParents    = new ArrayList();
	    _tmEntries    = new TreeMap(new CPTComparator());
	}

	public String toString() {
	    return "\n[CPT: " + _sChild + " / " + _alParents +
		" / Property: " + _sFunProperty + "\n" + _tmEntries;
	}
    }

    public static class CPTComparator 
	implements Comparator {

	public static CPTComparator _static = new CPTComparator();
	
	public int compare(Object o1, Object o2) {
	    ArrayList a1 = (ArrayList)o1;
	    ArrayList a2 = (ArrayList)o2;
	    if (a1.size() != a2.size()) {
		Object o = null; o.toString();
	    }
	    for (int i = 0; i < a1.size(); i++) {
		int val1 = ((Integer)a1.get(i)).intValue();
		int val2 = ((Integer)a2.get(i)).intValue();
		if (val1 < val2) {
		    return -1;
		} else if (val1 > val2) {
		    return 1;
		}
	    }
	    
	    // Must be equal!
	    return 0;
	}

    }

    //////////////////////////////////////////////////////////////
    //                       Main IR Parser
    //////////////////////////////////////////////////////////////
    public IR(InputStream is) {
	_lastToken = new Symbol(Symbol.IDENT, "NO VALID TOKENS YET", 0);
	_network = null;
	_lex = new Yylex(is);
	parse();
    }

    protected Symbol nextToken() {
	Symbol s = null;
	try {
	    while ((s = _lex.nextToken())._nID == Symbol.COMMENT);
	} catch (Exception e) {
	    System.out.println("Error while parsing: " + e);
	    System.out.println("Last token: " + _lastToken);
	    System.exit(1);
	}
	_lastToken = s;
	return s;
    }

    public void parse() {
	Symbol s = null;
	while ((s = nextToken()) != null && s._nID != Symbol.EOF) {
	    //System.out.println(s);
	    if (s._nID == Symbol.SEMI) {
		continue; // Unexpected SEMI but just skip
	    } else if (s._nID != Symbol.IDENT) {
	    	System.out.println("Error while parsing: {net|var|prob} expected, " +
				   s + " found.");
		System.exit(1);
	    }
	    if (((String)s._value).equalsIgnoreCase("network")) {
		_network = parseNetwork();

	    } else if (((String)s._value).equalsIgnoreCase("variable")) {
		Variable v = parseVariable();
		_network._hmVariables.put(v._sName, v);

	    } else if (((String)s._value).equalsIgnoreCase("probability")) {
		CPT cpt = parseCPT();
		_network._hmCPTs.put(cpt._sChild, cpt);

	    } else {
	    	System.out.println("Error while parsing: {net|var|prob} expected, " +
				   s + " found.");
		System.exit(1);
	    }
	}
    }

    public Network parseNetwork() {
	Symbol s = nextToken();
	Network n = new Network((String)s._value);
	match(Symbol.LCBRACE);
	while ((s = nextToken())._nID != Symbol.RCBRACE);
	return n;
    } 
    
    public Variable parseVariable() {
	Symbol s = nextToken();
	Variable v = new Variable((String)s._value);
	match(Symbol.LCBRACE);

	while ((s = nextToken())._nID == Symbol.IDENT) {
	    if (((String)s._value).equalsIgnoreCase("property")) {

		s = nextToken();
		if ("label".equalsIgnoreCase((String)s._value)) {
		    match(Symbol.EQUAL);
		    v._sLabel = nextToken()._value.toString();
		    match(Symbol.SEMI);
		} else {
		    while ((s = nextToken())._nID != Symbol.SEMI);
		}

	    } else if (((String)s._value).equalsIgnoreCase("type")) {

		match("discrete");
		match(Symbol.LBRACK);
		int nvals = ((Integer)nextToken()._value).intValue();
		match(Symbol.RBRACK);
		s = nextToken();
		if (s._nID == Symbol.EQUAL) {
		    match(Symbol.LCBRACE);
		} else {
		    if (s._nID != Symbol.LCBRACE) {
			System.out.println("Error while parsing: '=' or '{' expected, " +
					   s + " found.");
			Object o = null; o.toString();
			System.exit(1);
		    }
		}
		s = nextToken();
		//System.out.println(s);
		for (int i=0; i < nvals; i++) {
		    //System.out.println(s);
		    v._alValues.add(s._value.toString());
		    s = nextToken();
		    //System.out.println(s);
		    if (s._nID == Symbol.COMMA) {
			s = nextToken(); // Advance one more
		    }
		}
		match(Symbol.SEMI);
		
	    } else {
	    	System.out.println("Error while parsing: {property|type} expected, " +
				   s + " found.");
		Object o = null; o.toString();
		System.exit(1);
	    }
	}
	match(s, Symbol.RCBRACE);

	return v;
    }

    public CPT parseCPT() {
	match(Symbol.LPAREN);
	CPT cpt = new CPT(nextToken()._value.toString());
	System.out.print("- Loading CPT for " + cpt._sChild);
	Symbol s = null;
	while ((s = nextToken())._nID != Symbol.RPAREN) {
	    if (s._nID == Symbol.IDENT || s._nID == Symbol.INTEGER) {
		cpt._alParents.add(s._value.toString());
	    }
	} 

	match(Symbol.LCBRACE);
	s = nextToken();
	if (s._nID == Symbol.IDENT) {
	    if ("property".equalsIgnoreCase(s._value.toString())) {
		match("function");
		cpt._sFunProperty = nextToken()._value.toString();
		match(Symbol.SEMI);
		s = nextToken();
	    }
	}

	if (s._nID == Symbol.IDENT) {
	    match(s, "table");
	    cpt._sFunProperty = "table";

	    // Read off entries and put into _tmMap
	    // Entries start from v_0=0 ... v_n=0
	    //                    v_0=0 ... v_n=1
	    //                    ...   ...   ...
	    //                    v_0=j ... v_n=k
	    
	    // 1) Read all entries
	    // 2) Pass to a function which can recursively
	    //    generate labels from last to first and
	    //    enter the label and value into the entry 
	    //    table
	    // 3) Should verify correct number of entries
	    ArrayList entries = new ArrayList();
	    while ((s = nextToken())._nID != Symbol.SEMI) {
		if (s._nID == Symbol.DOUBLE) {
		    entries.add((Double)s._value);
		} else if (s._nID == Symbol.INTEGER) {
		    entries.add(new Double(((Integer)s._value).doubleValue()));
		} else {
		    match(s, Symbol.COMMA);
		}
	    }	    
	    ArrayList vars = new ArrayList();
	    vars.add(cpt._sChild);
	    vars.addAll(cpt._alParents);
	    ArrayList cur_assign = new ArrayList();
	    for (int i=0; i<vars.size(); i++) { cur_assign.add(null); }
	    genPTable(cpt._tmEntries, entries.iterator(),
		      cur_assign, vars, 0);
	    
	    // Sanity check
	    if (cpt._tmEntries.size() != entries.size()) {
		System.out.println("Table: " + cpt);
		System.out.println("Error: Table entries did not match expected size");
		System.out.println("Expected: " + cpt._tmEntries.size() + 
				   ", Actual: " + entries.size());
		System.exit(1);
	    }

	    match(Symbol.RCBRACE);

	} else {
	    
	    if (cpt._sFunProperty == null) {
		cpt._sFunProperty = "enum";
	    }

	    // Read off entries and put into _tmMap...
	    // ensure correct order.  Make sure max
	    // entries go here as well.

	    // Process each line - assignment first
	    while (s._nID != Symbol.RCBRACE) {
		match(s, Symbol.LPAREN);
		s = nextToken();
		ArrayList assign = new ArrayList();
		for (int i = 0; i < cpt._alParents.size(); i++) {
		    assign.add(s._value.toString());
		    s = nextToken();
		    if (s._nID == Symbol.COMMA) {
			s = nextToken();
		    }
		}
		match(s, Symbol.RPAREN);

		// Now read values
		ArrayList entries = new ArrayList();
		while ((s = nextToken())._nID != Symbol.SEMI) {
		    if (s._nID == Symbol.DOUBLE) {
			entries.add((Double)s._value);
		    } else if (s._nID == Symbol.INTEGER) {
			entries.add(new Double(((Integer)s._value).doubleValue()));
		    } else {
			match(s, Symbol.COMMA);
		    }
		}

		// Sanity check
		int nentries = _network.getNumValues(cpt._sChild);
		if (nentries != entries.size()) {
		    System.out.println("Table: " + cpt);
		    System.out.println("Error: Table entries did not match expected size");
		    System.out.println("Expected: " + nentries + 
				       ", Actual: " + entries.size());
		    System.exit(1);
		}

		// Generate entries
		Iterator ent = entries.iterator();
		for (int i = 0; i < nentries; i++) {
		    ArrayList indices = _network.values2Indices(cpt._alParents, assign);
		    indices.add(0, new Integer(i));
		    cpt._tmEntries.put(indices, ent.next());
		    //System.out.println(assign);
		    //System.out.println("Entered: " + indices + " -> ...");
		}

		// Advance to next token
		s = nextToken();
	    }   
	}

	System.out.println("... done");

	return cpt;
    }

    public void genPTable(TreeMap dest, Iterator entries, 
			  ArrayList cur_assign, ArrayList vars, int var_index) {

	// Iterate through all values at this index
	int max_ent = _network.getNumValues((String)vars.get(var_index));
	for (int i = 0; i < max_ent; i++) {

	    // Set this assignment
	    cur_assign.set(var_index, new Integer(i));
	    
	    // Are we at the last index?
	    if (var_index < (vars.size()-1)) {
		
		// Continue with rest of table
		genPTable(dest, entries, cur_assign, vars, var_index+1);

	    } else {
		
		// At last index so enter probability
		dest.put((ArrayList)cur_assign.clone(), entries.next());
		//System.out.println("Entered: " + cur_assign + " -> ...");
	    }
	}
    }

    public void match(int sym) {
	match(nextToken(), sym);
    }

    public void match(Symbol s, int sym) {
	if (s._nID != sym) {
	    System.out.println("Error while parsing: " + new Symbol(sym,null,-1) + 
			       " expected, " + s + " found.");
	    Object o = null; o.toString();
	    System.exit(1);
	}
    }

    public void match(String str) {
	match(nextToken(), str);
    }

    public void match(Symbol s, String str) {
	if (!str.equalsIgnoreCase((String)s._value)) {
	    System.out.println("Error while parsing: '" + str + "' expected, " +
			       s + " found.");
	    Object o = null; o.toString();
	    System.exit(1);		    
	}
    }

    public String toString() {
       return _network.toString();
    }

    //////////////////////////////////////////////////////////////
    //                      Testing Functions
    //////////////////////////////////////////////////////////////
    public static void main(String[] args) {
	if (args.length != 1) {
	    System.out.println("Must provide filename (file in bif format)");
	    System.exit(1);
	}
	IR ir = null;
	try {
	    ir = new IR(new FileInputStream(args[0]));
	} catch (IOException e) {
	    System.out.println("Exception: " + e );
	    System.exit(1);
	}
	
	// Generate dot file for this Bayes net
	String file_short = args[0].substring(0,args[0].length()-4);
	ir.genDot(file_short + ".dot");

	// Show IR contents
	System.out.println(ir);
    }

    //////////////////////////////////////////////////////////////
    //                    Graph Visualization
    //////////////////////////////////////////////////////////////
    public void genDot(String filename) {

	// Build a graph
	Graph g = new Graph();
	Iterator i = _network._hmVariables.keySet().iterator();
	while (i.hasNext()) {
	    String v = (String)i.next();
	    g.addNode(v);
	    CPT cpt_for_v = ((CPT)_network._hmCPTs.get(v));
	    if (cpt_for_v == null) {
		continue;
	    }
	    g.addUniLinksFrom(cpt_for_v._alParents, v);
	}

	// Dump it to a file
	g.genDotFile(filename);
    }
}
