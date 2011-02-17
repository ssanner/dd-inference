package logic.add;

import graph.Graph;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;



//Builds 
public class TestNumericalPrecision {


    public static ArrayList tree;
    public static ArrayList testTree;
    public static ArrayList alOrder;
    public static HashMap   var2ID;
    public static ArrayList mn(int i) { 
	ArrayList l = new ArrayList();
	l.add(new BigDecimal(""+i));
	return l;
    }

    //Builds a tree to test on.  2 is 16e + 8d + 4c + 2b + a, 1 is 2 levels, 0 is a simple decision 0 
    																						//	   1  2
    public static ArrayList buildTestTree(int type){
    	
    	alOrder.add(new Integer(1));
    	alOrder.add(new Integer(2));
    	alOrder.add(new Integer(3));
    	alOrder.add(new Integer(4));
    	alOrder.add(new Integer(5));
    	
	var2ID = new HashMap();
	var2ID.put("a", new Integer(1));
	var2ID.put("b", new Integer(2));
	var2ID.put("c", new Integer(3));
	var2ID.put("d", new Integer(4));
	var2ID.put("e", new Integer(5));
	
	if (type == 2){
	
/**		left high, right low						                   	a 
									b                                                    b
    		c                          c                           c                             c
	d            d             d             d             d              d              d            d
 e      e      e     e      e      e      e      e      e      e       e      e       e      e        e        e
0  16  8  24  4  20 12 28  2  18  10 26  6  22  14 30  1  17  9  25   5  21  13 29   3  19  11 27   7 23  15 31
**/
	ArrayList tree31 = new ArrayList();
	tree31.add("e"); tree31.add(mn(31)); tree31.add(mn(15));
	ArrayList tree30 = new ArrayList();
	tree30.add("e"); tree30.add(mn(23)); tree30.add(mn(7));
	ArrayList tree29 = new ArrayList();
	tree29.add("e"); tree29.add(mn(27)); tree29.add(mn(11));
	ArrayList tree28 = new ArrayList();
	tree28.add("e"); tree28.add(mn(19)); tree28.add(mn(3));
	ArrayList tree27 = new ArrayList();
	tree27.add("e"); tree27.add(mn(29)); tree27.add(mn(13));
	ArrayList tree26 = new ArrayList();
	tree26.add("e"); tree26.add(mn(21)); tree26.add(mn(5));
	ArrayList tree25 = new ArrayList();
	tree25.add("e"); tree25.add(mn(25)); tree25.add(mn(9));
	ArrayList tree24 = new ArrayList();
	tree24.add("e"); tree24.add(mn(17)); tree24.add(mn(1));
	ArrayList tree23 = new ArrayList();
	tree23.add("e"); tree23.add(mn(30)); tree23.add(mn(14));
	ArrayList tree22 = new ArrayList();
	tree22.add("e"); tree22.add(mn(22)); tree22.add(mn(6));
	ArrayList tree21 = new ArrayList();
	tree21.add("e"); tree21.add(mn(26)); tree21.add(mn(10));
	ArrayList tree20 = new ArrayList();
	tree20.add("e"); tree20.add(mn(18)); tree20.add(mn(2));
	ArrayList tree19 = new ArrayList();
	tree19.add("e"); tree19.add(mn(28)); tree19.add(mn(12));
	ArrayList tree18 = new ArrayList();
	tree18.add("e"); tree18.add(mn(20)); tree18.add(mn(4));
	ArrayList tree17 = new ArrayList();
	tree17.add("e"); tree17.add(mn(24)); tree17.add(mn(8));
	ArrayList tree16 = new ArrayList();
	tree16.add("e"); tree16.add(mn(16)); tree16.add(mn(0));
	
	ArrayList tree15 = new ArrayList();
	tree15.add("d"); tree15.add(tree31); tree15.add(tree30);
	ArrayList tree14 = new ArrayList();
	tree14.add("d"); tree14.add(tree29); tree14.add(tree28);
	ArrayList tree13 = new ArrayList();
	tree13.add("d"); tree13.add(tree27); tree13.add(tree26);
	ArrayList tree12 = new ArrayList();
	tree12.add("d"); tree12.add(tree25); tree12.add(tree24);
	ArrayList tree11 = new ArrayList();
	tree11.add("d"); tree11.add(tree23); tree11.add(tree22);
	ArrayList tree10 = new ArrayList();
	tree10.add("d"); tree10.add(tree21); tree10.add(tree20);
	ArrayList tree9 = new ArrayList();
	tree9.add("d"); tree9.add(tree19); tree9.add(tree18);
	ArrayList tree8 = new ArrayList();
	tree8.add("d"); tree8.add(tree17); tree8.add(tree16);

	ArrayList tree7 = new ArrayList();
	tree7.add("c"); tree7.add(tree15); tree7.add(tree14);
	ArrayList tree6 = new ArrayList();
	tree6.add("c"); tree6.add(tree13); tree6.add(tree12);
	ArrayList tree5 = new ArrayList();
	tree5.add("c"); tree5.add(tree11); tree5.add(tree10);
	ArrayList tree4 = new ArrayList();
	tree4.add("c"); tree4.add(tree9); tree4.add(tree8);
	
	ArrayList tree3 = new ArrayList();
	tree3.add("b"); tree3.add(tree7); tree3.add(tree6);
	ArrayList tree2 = new ArrayList();
	tree2.add("b"); tree2.add(tree5); tree2.add(tree4);
	

	testTree.add("a"); testTree.add(tree3); testTree.add(tree2);
	}
	
	if (type == 1){
	ArrayList testTree1 = new ArrayList();
	testTree1.add("b"); testTree1.add(mn(2)); testTree1.add(mn(3));
	ArrayList testTree2 = new ArrayList();
	testTree2.add("b"); testTree2.add(mn(0)); testTree2.add(mn(1));
	
	testTree.add("a"); testTree.add(testTree1); testTree.add(testTree2);
	}
	
	if (type ==0){
	//Simple Test tree
	testTree = new ArrayList();
	testTree.add("a"); testTree.add(mn(1)); testTree.add(mn(2));
	}
	
	return testTree;
    }
    
    public static void main(String[] args) {
    	errorTest(0, false);
    	
    }
    
    //Builds an ADD, AADD, LAADD for the given tree type, 
    public static void errorTest(int type, Boolean print){
  
    	DD add = new ADD(alOrder);
    	
    	int add1 = add.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int addresult = operateMany(add, add1, DD.ARITH_PROD,0);
    	
    	
    	
    
    	DD aadd = new AADD(alOrder);
    	int aadd1 = aadd.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int aaddresult = operateMany(aadd, aadd1, DD.ARITH_PROD, 0);
    	
    	
            	
    	DD laadd = new LAADD(alOrder);
    	int laadd1 = laadd.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int laaddresult = operateMany(laadd, laadd1, DD.ARITH_PROD, 0);
   
    	
    	if (print){
    		Graph g1 = add.getGraph(addresult);
        	g1.launchViewer(1300, 770);
        	Graph g2= aadd.getGraph(aaddresult);
        	g2.launchViewer(1300, 770);
        	Graph g3 = laadd.getGraph(laadd1);
        	g3.launchViewer(1300, 770);
    	}
    	
    	
    	//Evaluates each possible assignation.  still done manual
    	//*TODO Change to it depends on the tree, rather than manually change
    	ArrayList assigns = new ArrayList(); 	
    	for (int i = 0; i <= 1; i++){
    		assigns.clear();
    		//assigns.add(toBool(((i >> 4)) % 2));
    		//assigns.add(toBool(((i >> 3)) % 2));
    		//assigns.add(toBool(((i >> 2)) % 2));
   // 		assigns.add(toBool(((i >> 1)) % 2));
    		assigns.add(toBool(((i >> 0)) % 2));
    		System.out.println(Math.exp(laadd.evaluate(laadd1, assigns)) + " " + aadd.evaluate(aadd1, assigns));
    	//	System.out.println("ADD: " + add.evaluate(addresult, assigns)+  " = " + aadd.evaluate(aaddresult, assigns) + " Difference: " + 100*(( aadd.evaluate(aaddresult, assigns) - add.evaluate(addresult, assigns))/aadd.evaluate(aaddresult, assigns)) );
    		

    	//System.out.println("Difference ADD/AADD: " + ((aadd.evaluate(aaddresult, assigns) - add.evaluate(addresult, assigns)))/(add.evaluate(aaddresult, assigns))*100);
    //	System.out.println("Difference ADD/LAADD: " + (add.evaluate(addresult, assigns) - laadd.evaluate(laaddresult, assigns)));
    //	System.out.println("--------------------------------");
    	}

    	
    }
    

    public static Boolean toBool(int i) {
    	return (i == 1);
    }
    
    
    //Applies and Reapplices an operation to a given node.  Returns the final node.
    public static int operateMany(DD context, int topNode, int op, int numOps){
    	int ret = 0;
    	int temp = temp = context.applyInt(topNode, topNode, op);
    	ret = temp;
    	for (int i = 1; i <= numOps; i++){
    		temp = context.applyInt(temp, temp, op);
    		ret = temp;
    	}
    	return ret;
    }
    
	
}
