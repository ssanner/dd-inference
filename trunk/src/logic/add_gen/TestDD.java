//////////////////////////////////////////////////////////////////
//                    Testing Methods for DD
//////////////////////////////////////////////////////////////////

package logic.add_gen;

import java.math.*;
import java.util.*;

import graph.Graph;

public class TestDD {

    public static ArrayList tree;
    public static HashMap   var2ID;
    public static ArrayList mn(int i) { 
	ArrayList l = new ArrayList();
	l.add(new BigDecimal(""+i));
	return l;
    }

    static {
	var2ID = new HashMap();
	var2ID.put("a", new Integer(1));
	var2ID.put("b", new Integer(2));
	var2ID.put("c", new Integer(3));
	
	//        /h: tree2:c [0,1]   h:tree5:c [4,5]
	// tree:a                  /   
	//        \l:   tree3:b
	//                         \  l:tree6:c [9,10]
	//
	// ==> [10 9 5 4 1 0 1 0] (0..7)
	ArrayList tree5 = new ArrayList();
	tree5.add("c"); tree5.add(mn(4)); tree5.add(mn(5));
	ArrayList tree6 = new ArrayList();
	tree6.add("c"); tree6.add(mn(9)); tree6.add(mn(10));
	ArrayList tree2 = new ArrayList();
	tree2.add("c"); tree2.add(mn(0)); tree2.add(mn(1));

	ArrayList tree3 = new ArrayList();
	tree3.add("b"); tree3.add(tree5); tree3.add(tree6);
	tree = new ArrayList();
	tree.add("a"); tree.add(tree2); tree.add(tree3);
    }
    
    public static void main(String[] args) {

	// Perform each test
//	testDD(DD.TYPE_TABLE);
//	testDD(DD.TYPE_ADD);
	testDD(DD.TYPE_AADD);
    }

    public static void testDD(int type) {

	System.out.println("\nPerforming DD test 1:\n-----------------------\n");

	// Build the first DD
	ArrayList alOrder = new ArrayList(); // ordering of prop vars (must occur first!)
	alOrder.add(new Integer(1));
	alOrder.add(new Integer(2));
	alOrder.add(new Integer(3));
	DD a;
	switch (type) {
	case DD.TYPE_TABLE: {
	    a = new Table(alOrder);
	} break;
	case DD.TYPE_ADD: {
	    a = new ADD(alOrder);
	} break;
	case DD.TYPE_AADD: {
	    a = new AADD(alOrder);
	} break;
	default: {
	    System.out.println("Illegal TYPE");
	    System.exit(1);
	    a = null;
	}
	}

	// Low node comes first!
	int a1 = a.getVarNode(1, 0d, 4d);
	int a2 = a.getVarNode(2, 0d, 2d);
	int a3 = a.getVarNode(3, 0d, 1d);
	a.addSpecialNode(a1);
	a.addSpecialNode(a2);
	a.addSpecialNode(a3);
	
	// Show current DDs
	System.out.println("DD_1:\n" + a.printNode(a1)); 
	System.out.println("DD_2:\n" + a.printNode(a2));
	System.out.println("DD_3:\n" + a.printNode(a3));

	// Apply the SUM op
	int tmp = a.applyInt(a2, a3, DD.ARITH_PROD);
	a.flushCaches(true);
	int a4 = a.applyInt(a2, a3, DD.ARITH_SUM);
	System.out.println("\nDD_4 = DD_2 + DD_3:\n" + a.printNode(a4));

	// Apply the SUM op again
	int a5 = a.applyInt(a1, a4, DD.ARITH_SUM);
	a.addSpecialNode(a5);
	System.out.println("\nDD_5 = DD_1 + DD_4:\n" + a.printNode(a5));
	DD.PrintEnum(a,a5);
	


	// Apply the SUM op once more
	a.flushCaches(true);
	int a6 = a.applyInt(a5, a5, DD.ARITH_SUM);
	System.out.println("\n**Efficiency of square**: DD_6 = DD_5 + DD_5:\n" + a.printNode(a6));
	DD.PrintEnum(a,a6);

	// Apply the PROD op
	int a7 = a.applyInt(a5, a5, DD.ARITH_PROD);
	System.out.println("\nDD_7 = DD_5 * DD_5:\n" + a.printNode(a7)); 
	DD.PrintEnum(a,a7);

	// Apply the MIN op
	int a8 = a.applyInt(a6, a7, DD.ARITH_MIN);
	System.out.println("\nDD_8 = min(DD_6, DD_7):\n" + a.printNode(a8));
	DD.PrintEnum(a,a8);

	// Apply the MAX op
	int a9 = a.applyInt(a6, a7, DD.ARITH_MAX);
	System.out.println("\nDD_9 = max(DD_6, DD_7):\n" + a.printNode(a9));
	DD.PrintEnum(a,a9);

	// Apply the PROD op
	int a10 = a.applyInt(a.applyInt(a1, a2, DD.ARITH_PROD), 
			     a3, DD.ARITH_PROD);
	System.out.println("\nDD_10 = PROD DD_{1,2,3}:\n" + a.printNode(a10));
	DD.PrintEnum(a,a10);

	// Sum out a9
	int a11 = a.opOut(a.opOut(a.opOut(a9, 1, DD.ARITH_SUM), 
				  3, DD.ARITH_SUM), 2, DD.ARITH_SUM);
	System.out.println("\nDD_11 = SUM_{1,2,3} A9:\n" + a.printNode(a11));
	DD.PrintEnum(a,a11);

	// Test buildDD (unordered)
	int a12 = a.buildDDFromOrderedTree(tree, var2ID);
	System.out.println("\nDD_12 = BUILD ORDER:\n" + a.printNode(a12));
	DD.PrintEnum(a,a12);

	//Graph g1 = a.getGraph(a12);
//	g1.launchViewer(1300, 770);
	
	// Test buildDD (ordered)
	int a13 = a.buildDDFromUnorderedTree(tree, var2ID);
	System.out.println("\nDD_13 = BUILD UNORDER:\n" + a.printNode(a13));
	DD.PrintEnum(a,a13);
	a.pruneReport();
	
	int a14 = a.applyInt(a12, a12, DD.ARITH_PROD);
	int a15 = a.applyInt(a14, a12, DD.ARITH_DIV);
	
	Graph g1 = a.getGraph(a12);
	g1.launchViewer(1300, 770);
	
	Graph g2 = a.getGraph(a15);
	g2.launchViewer(1300, 770);
	
    }
    
    
}
