//////////////////////////////////////////////////////////////////
//                    Testing Methods for ADD
//////////////////////////////////////////////////////////////////

package logic.add_gen;

import java.util.*;

public class TestADD {
    
    // General testing methods for the ADD class
    public static void main(String[] args) {

	// Perform each test
	testADD1();
	testADD2();
	//testSwap();
	testADD3();
	new ADD(new ArrayList()).pruneReport();
    }

    // This tests the binary operations
    public static void testADD1() {

	System.out.println("\nPerforming ADD test 1:\n-----------------------\n");

	// Build the first ADD
	ArrayList alOrder = new ArrayList(); // ordering of prop vars (must occur first!)
	alOrder.add(new Integer(1));
	alOrder.add(new Integer(2));
	alOrder.add(new Integer(3));
	ADD a = new ADD(alOrder);

	// Low node comes first!
	int a1 = a.getVarNode(1, 0d, 4d);
	int a2 = a.getVarNode(2, 0d, 2d);
	int a3 = a.getVarNode(3, 0d, 1d);
	a.addSpecialNode(a1);
	a.addSpecialNode(a2);
	a.addSpecialNode(a3);
	
	// Show current ADDs
	System.out.println("ADD_1:\n" + a.getNode(a1).toString(a,0));
	System.out.println("ADD_2:\n" + a.getNode(a2).toString(a,0));
	System.out.println("ADD_3:\n" + a.getNode(a3).toString(a,0));

	// Apply the SUM op
	a.flushCaches(true);
	int a4 = a.applyInt(a2, a3, ADD.ARITH_SUM);
	System.out.println("\nADD_4 = ADD_2 + ADD_3:\n" + a.getNode(a4).toString(a,0));
	int tmp = a.applyInt(a2, a4, ADD.ARITH_PROD);

	// Apply the SUM op again
	int a5 = a.applyInt(a1, a4, ADD.ARITH_SUM);
	a.addSpecialNode(a5);
	System.out.println("\nADD_5 = ADD_1 + ADD_4:\n" + a.getNode(a5).toString(a,0));	
	//PrintEnum(a5);

	// Apply the SUM op once more
	a.flushCaches(true);
	int a6 = a.applyInt(a5, a5, ADD.ARITH_SUM);
	System.out.println("\n**Efficiency of square**: ADD_6 = ADD_5 + ADD_5:\n" + a.getNode(a6).toString(a,0));
	//PrintEnum(a6);

	// Apply the PROD op
	int a7 = a.applyInt(a5, a5, ADD.ARITH_PROD);
	System.out.println("\nADD_7 = ADD_5 * ADD_5:\n" + a.getNode(a7).toString(a,0));
	//PrintEnum(a7);

	// Apply the MIN op
	int a8 = a.applyInt(a6, a7, ADD.ARITH_MIN);
	System.out.println("\nADD_8 = min(ADD_6, ADD_7):\n" + a.getNode(a8).toString(a,0));
	//PrintEnum(a8);

	// Apply the MAX op
	int a9 = a.applyInt(a6, a7, ADD.ARITH_MAX);
	System.out.println("\nADD_9 = max(ADD_6, ADD_7):\n" + a.getNode(a9).toString(a,0));
	//PrintEnum(a9);

	// Apply the PROD op
	int a10 = a.applyInt(a.applyInt(a1, a2, ADD.ARITH_PROD), 
			     a3, ADD.ARITH_PROD);
	System.out.println("\nADD_10 = PROD ADD_{1,2,3}:\n" + a.getNode(a10).toString(a,0));
	//PrintEnum(a10);
    }
    

    // This tests the binary operations
    public static void testADD2() {

	System.out.println("\nPerforming ADD test 2:\n-----------------------\n");

	// Build the first ADD
	ArrayList alOrder = new ArrayList(); // ordering of prop vars (must occur first!)
	alOrder.add(new Integer(1));
	alOrder.add(new Integer(2));
	alOrder.add(new Integer(3));
	alOrder.add(new Integer(4));
	alOrder.add(new Integer(5));
	ADD a1 = new ADD(alOrder);
	ADD a2 = new ADD(alOrder);
	ADD a3 = new ADD(alOrder);
	ADD a4 = new ADD(alOrder);
	ADD a5 = new ADD(alOrder);

	// Low node comes first!
	int n1 = a1.getVarNode(1, 0d, 1d);
	int n2 = a2.getVarNode(2, 0d, 1d);
	int n3 = a3.getVarNode(3, 0d, 1d);
	int n4 = a4.getVarNode(4, 0d, 1d);
	int n5 = a5.getVarNode(5, 0d, 1d);
	a1.setRoot(n1);
	a2.setRoot(n2);
	a3.setRoot(n3);
	a4.setRoot(n4);
	a5.setRoot(n5);
	
	// Show current ADDs
	System.out.println("ADD_1:\n" + a1);
	System.out.println("ADD_2:\n" + a2);
	System.out.println("ADD_3:\n" + a3);
	System.out.println("ADD_4:\n" + a4);
	System.out.println("ADD_5:\n" + a5);

	// Apply the SUM op
	ADD a6 = ADD.Apply(ADD.Apply(ADD.Apply(ADD.Apply(a1, a2, ADD.ARITH_SUM), 
			     a3, ADD.ARITH_SUM), a4, ADD.ARITH_SUM), a5, ADD.ARITH_SUM);
	System.out.println("\nADD_6 = SUM ADD_{1,2,3,4,5}:\n" + a6);
	PrintEnum(a6);

	// Apply the PROD op
	ADD a7 = ADD.Apply(ADD.Apply(ADD.Apply(ADD.Apply(a1, a2, ADD.ARITH_PROD), 
			     a3, ADD.ARITH_PROD), a4, ADD.ARITH_PROD), a5, ADD.ARITH_PROD);
	System.out.println("\nADD_7 = PROD ADD_{1,2,3,4,5}:\n" + a7);
	PrintEnum(a7);

	// Apply the MIN op
	ADD a8 = ADD.Apply(a3, a6, ADD.ARITH_MIN);
	System.out.println("\nADD_8 = MIN( ADD_3, ADD_6 ):\n" + a8);
	PrintEnum(a8);

	// Apply the MAX op
	ADD a9 = ADD.Apply(a3, a6, ADD.ARITH_MAX);
	System.out.println("\nADD_9 = MAX( ADD_3, ADDD_6 ):\n" + a9);
	PrintEnum(a9);

	// Apply the DIV op
	ADD a10 = a6.scalarAdd(1.0d).invert();
	System.out.println("\nADD_10 = 1/(ADD_6+1):\n" + a10);
	PrintEnum(a10);

	// Final reality check
	ADD a11 = ADD.Apply(a6.scalarAdd(1.0d), a10, ADD.ARITH_PROD);
	System.out.println("\nADD_11 = (ADD_6+1) * 1/(ADD_6+1):\n" + a11);
	PrintEnum(a11);	
    }

    // Function for testing order swap correctness
    public static void testSwap() {

	System.out.println("\nPerforming ADD test swap:\n--------------------------\n");

	// Build the first ADD
	ArrayList alOrder = new ArrayList(); // ordering of prop vars (must occur first!)
	alOrder.add(new Integer(1));
	alOrder.add(new Integer(2));
	alOrder.add(new Integer(3));
	alOrder.add(new Integer(4));
	alOrder.add(new Integer(5));
	ADD a1 = new ADD(alOrder);
	ADD a2 = new ADD(alOrder);
	ADD a3 = new ADD(alOrder);
	ADD a4 = new ADD(alOrder);
	ADD a5 = new ADD(alOrder);

	// Low node comes first!
	int n1 = a1.getVarNode(1, 0d, 1d);
	int n2 = a2.getVarNode(2, 0d, 1d);
	int n3 = a3.getVarNode(3, 0d, 1d);
	int n4 = a4.getVarNode(4, 0d, 1d);
	int n5 = a5.getVarNode(5, 0d, 1d);
	a1.setRoot(n1);
	a2.setRoot(n2);
	a3.setRoot(n3);
	a4.setRoot(n4);
	a5.setRoot(n5);
	
	// Apply the DIV op
	ADD a6 = ADD.Apply(ADD.Apply(ADD.Apply(ADD.Apply(a1, a2, ADD.ARITH_SUM), 
			     a3, ADD.ARITH_SUM), a4, ADD.ARITH_SUM), a5, ADD.ARITH_SUM);
	ADD a10 = a6.scalarAdd(1.0d).invert();
	System.out.println("\nADD_10 = 1/(AAAD_6+1):\n" + a10);
	PrintEnum(a10);

	// Test variable swapping on a10!!!
	//System.out.println("\nA10-orig:\n" + a10);
	//PrintEnum(a10);
	//a10.swapVertex(0);
	//PrintEnum(a10);
	//a10.swapVertex(1);
	//PrintEnum(a10);
	//a10.swapVertex(2);
	//PrintEnum(a10);
	//System.out.println("\nA10-sw:\n" + a10);

	//a10.reduce();
	//System.out.println("\nA10-sw-r:\n" + a10);
	//PrintEnum(a10);
	//System.out.println("\nReality check: should be 1!\n");
	//ADD ainterm = ADD.Apply(a6.scalarAdd(1.0d), a10, ADD.ARITH_PROD);
	//System.out.println(ainterm);
	//PrintEnum(ainterm);
	//a10.swapVertex(2);
	//a10.swapVertex(1);
	//a10.swapVertex(0);
	//System.out.println("\nA10-sw-back:\n" + a10);
	//PrintEnum(a10);
	//System.out.println("\nReality check: should be 1!\n");
	//ADD afinal = ADD.Apply(a6.scalarAdd(1.0d), a10, ADD.ARITH_PROD);

	// Should be 1 if correct!
	//System.out.println(afinal);
	//afinal.reduce();
	//System.out.println(afinal);
	//PrintEnum(afinal);  
    }

    public static void testADD3() {
	System.out.println("\nPerforming ADD test 2:\n-----------------------\n");

	// Build the first ADD
	ArrayList alOrder1 = new ArrayList(); // ordering of prop vars (must occur first!)
	ArrayList alOrder2 = new ArrayList(); // ordering of prop vars (must occur first!)
	alOrder1.add(new Integer(1)); 
	alOrder1.add(new Integer(2)); 
	alOrder1.add(new Integer(3));
	alOrder2.add(new Integer(3)); 
	alOrder2.add(new Integer(2)); 
	alOrder2.add(new Integer(1));
	ADD a1_1 = new ADD(alOrder1); 
	ADD a2_1 = new ADD(alOrder1); 
	ADD a3_1 = new ADD(alOrder1);
	ADD a1_2 = new ADD(alOrder2); 
	ADD a2_2 = new ADD(alOrder2); 
	ADD a3_2 = new ADD(alOrder2);

	// Low node comes first!
	int n1_1 = a1_1.getVarNode(1, 0d, 1d);
	int n2_1 = a2_1.getVarNode(2, 0d, 1d);
	int n3_1 = a3_1.getVarNode(3, 0d, 1d);
	a1_1.setRoot(n1_1);
	a2_1.setRoot(n2_1);
	a3_1.setRoot(n3_1);
	int n1_2 = a1_2.getVarNode(1, 0d, 1d);
	int n2_2 = a2_2.getVarNode(2, 0d, 1d);
	int n3_2 = a3_2.getVarNode(3, 0d, 1d);
	a1_2.setRoot(n1_2);
	a2_2.setRoot(n2_2);
	a3_2.setRoot(n3_2);
	
	// Show current ADDs
	ADD a1 = ADD.Apply(ADD.Apply(a1_1, a2_1, ADD.ARITH_SUM), a3_1, ADD.ARITH_SUM);
	ADD a2 = ADD.Apply(ADD.Apply(a1_2, a2_2, ADD.ARITH_SUM), a3_2, ADD.ARITH_SUM).negate();
	System.out.println("\nA1:\n" + a1);
	PrintEnum(a1);
	System.out.println("\nA2:\n" + a2);
	PrintEnum(a2);
	ADD a4 = new ADD(a1);
	ADD a5 = new ADD(a2);

	// Apply the SUM op
	ADD a3 = ADD.Apply(a1, a2, ADD.ARITH_SUM);
	System.out.println("\nA3 = A1 + A2:\n" + a3);
	PrintEnum(a3);

	// TODO: Now verify the sum out operation
	System.out.println("SUMOut A1:\n-------\n");
	System.out.println("\nStart:\n" + a1);
	PrintEnum(a1);
	a1.setRoot(a1.opOut(3, ADD.ARITH_SUM));	
	System.out.println("\nSum out 3:\n" + a1);
	a1.setRoot(a1.opOut(2, ADD.ARITH_SUM));
	System.out.println("\nSum out 2:\n" + a1);
	a1.setRoot(a1.opOut(1, ADD.ARITH_SUM));
	System.out.println("\nSum out 1:\n" + a1);
	PrintEnum(a1);

	// TODO: Now verify the sum out operation
	System.out.println("SUMOut A2:\n-------\n");
	System.out.println("\nStart:\n" + a2);
	PrintEnum(a2);
	a2.setRoot(a2.opOut(3, ADD.ARITH_SUM));	
	System.out.println("\nSum out 3:\n" + a2);
	a2.setRoot(a2.opOut(2, ADD.ARITH_SUM));
	System.out.println("\nSum out 2:\n" + a2);
	a2.setRoot(a2.opOut(1, ADD.ARITH_SUM));
	System.out.println("\nSum out 1:\n" + a2);
	PrintEnum(a2);

	// Verify the restrict operation on A4
	System.out.println("Restrict A4(A1) H/H/H:\n------------\n");
	System.out.println("\nStart:\n" + a4);
	PrintEnum(a4);
	a4.restrict(3, ADD.RESTRICT_HIGH);	
	System.out.println("\nRestrict 3:\n" + a4);
	a4.restrict(2, ADD.RESTRICT_HIGH);
	System.out.println("\nRestrict 2:\n" + a4);
	a4.restrict(1, ADD.RESTRICT_HIGH);
	System.out.println("\nRestrict 1:\n" + a4);
	PrintEnum(a4);

	// Verify the restrict operation on A5
	System.out.println("Restrict A5(A2) L/H/H:\n-------------\n");
	System.out.println("\nStart:\n" + a5);
	PrintEnum(a5);
	a5.restrict(3, ADD.RESTRICT_LOW);	
	System.out.println("\nRestrict 3:\n" + a5);
	a5.restrict(2, ADD.RESTRICT_HIGH);
	System.out.println("\nRestrict 2:\n" + a5);
	a5.restrict(1, ADD.RESTRICT_HIGH);
	System.out.println("\nRestrict 1:\n" + a5);
	PrintEnum(a5);
    }

    // Helper function to display output from all settings
    public static void PrintEnum(ADD a) {

	// Traverse all paths and verify output
	int nvars = a._alOrder.size();
	ArrayList assign = new ArrayList();
	Boolean TRUE  = new Boolean(true);
	Boolean FALSE = new Boolean(false);

	// Initialize assignment
	for (int c = 0; c < nvars; c++) {
	    assign.add(FALSE); 
	}
	
	// Now print table
	for (int c = 0; c < (1 << nvars); c++) {

	    // Set all bits
	    // c >> 0 is low bit which comes last (pos 2)
	    for (int b = nvars - 1; b >= 0; b--) {
		assign.set(b, (((c >> (nvars - b - 1)) & 1) == 1) ? TRUE : FALSE);
	    }

	    // Now show the assignment
	    System.out.println("Assignment: " + 
			       PrintBitVector(assign) + " -> " + 
			       a.evaluate(a._nRoot, assign));
	}
	System.out.println();

    }

    public static String PrintBitVector(ArrayList l) {
	StringBuffer sb = new StringBuffer("[ ");
	Iterator i = l.iterator();
	while (i.hasNext()) {
	    Boolean b = (Boolean)i.next();
	    sb.append( b.booleanValue() ? "1 " : "0 ");
	}
	sb.append("]");

	return sb.toString();
    }
}
