package logic.add_gen;

import graph.Graph;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
//Builds 
public class TestPrecision {

    public static ArrayList tree;
    public static ArrayList testTree;
    public static ArrayList alOrder;
    public static HashMap   var2ID;
    public static int N_var;
    public static ArrayList mn(int i) {
    	ArrayList l = new ArrayList();
    	l.add(new Double(i));
    	return l;
    //  	
    }
//    public static ArrayList mn(int i) { 
//	ArrayList l = new ArrayList();
//	l.add(new BigDecimal(""+i));
//	return l;
//    }

    public static void buildOrder(){
    	alOrder = new ArrayList();
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
    }
    
    //Builds a tree to test on. type: 2 is 16e + 8d + 4c + 2b + a, 1 is 2 levels, 0 is a simple decision 0 
	public static ArrayList buildTestTree(int type){
		
    	testTree = new ArrayList();
    	switch(type){
    	case 2: //16e + 8d + 4c + 2b + a
    		N_var = 5;
    		ArrayList tree31 = new ArrayList();
			tree31.add("e"); tree31.add(mn(32)); tree31.add(mn(16));
			ArrayList tree30 = new ArrayList();
			tree30.add("e"); tree30.add(mn(24)); tree30.add(mn(8));
			ArrayList tree29 = new ArrayList();
			tree29.add("e"); tree29.add(mn(28)); tree29.add(mn(12));
			ArrayList tree28 = new ArrayList();
			tree28.add("e"); tree28.add(mn(20)); tree28.add(mn(4));
			ArrayList tree27 = new ArrayList();
			tree27.add("e"); tree27.add(mn(30)); tree27.add(mn(14));
			ArrayList tree26 = new ArrayList();
			tree26.add("e"); tree26.add(mn(22)); tree26.add(mn(6));
			ArrayList tree25 = new ArrayList();
			tree25.add("e"); tree25.add(mn(26)); tree25.add(mn(10));
			ArrayList tree24 = new ArrayList();
			tree24.add("e"); tree24.add(mn(18)); tree24.add(mn(2));
			ArrayList tree23 = new ArrayList();
			tree23.add("e"); tree23.add(mn(31)); tree23.add(mn(15));
			ArrayList tree22 = new ArrayList();
			tree22.add("e"); tree22.add(mn(23)); tree22.add(mn(7));
			ArrayList tree21 = new ArrayList();
			tree21.add("e"); tree21.add(mn(27)); tree21.add(mn(11));
			ArrayList tree20 = new ArrayList();
			tree20.add("e"); tree20.add(mn(19)); tree20.add(mn(3));
			ArrayList tree19 = new ArrayList();
			tree19.add("e"); tree19.add(mn(29)); tree19.add(mn(13));
			ArrayList tree18 = new ArrayList();
			tree18.add("e"); tree18.add(mn(21)); tree18.add(mn(5));
			ArrayList tree17 = new ArrayList();
			tree17.add("e"); tree17.add(mn(25)); tree17.add(mn(9));
			ArrayList tree16 = new ArrayList();
			tree16.add("e"); tree16.add(mn(17)); tree16.add(mn(1));
			
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
			break;
			
    	case 1: // 2*a + (not)b
    		N_var = 2;
			ArrayList testTree1 = new ArrayList();
			testTree1.add("b"); testTree1.add(mn(3)); testTree1.add(mn(4));
			ArrayList testTree2 = new ArrayList();
			testTree2.add("b"); testTree2.add(mn(1)); testTree2.add(mn(2));

			testTree.add("a"); testTree.add(testTree1); testTree.add(testTree2);
			break;
	
    	case 0: //1 + (not)a
    		N_var = 1;
    		testTree.add("a"); testTree.add(mn(1)); testTree.add(mn(2));
    	}
	
    	return testTree;
    }
    
    public static void main(String[] args) {
    	errorTest2(2, true,1);
    }
    
    //Builds an ADD, AADD, LAADD for the given tree type, 
    public static void errorTest(int type, Boolean print,int N_OP){
    	buildOrder();
    	DD add = new ADD(alOrder); 	
    	int add2 = add.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int add1 = add.buildDDFromOrderedTree(buildTestTree(type+1), var2ID);
    	int atemp = operateMany(add, add1, DD.ARITH_SUM, N_OP, add2);
    	atemp = operateMany(add, atemp, DD.ARITH_MINUS,N_OP, add1);
    	atemp = operateMany(add, atemp, DD.ARITH_MINUS,N_OP, add2);
    	int ares = operateMany(add, atemp, DD.ARITH_SUM,N_OP, add1);
    	
    	DD aadd = new AADD(alOrder);
    	int aadd2 = aadd.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int aadd1 = aadd.buildDDFromOrderedTree(buildTestTree(type+1), var2ID);
    	int aatemp = operateMany(aadd, aadd1, DD.ARITH_SUM, N_OP, aadd2);
    	aatemp = operateMany(aadd, aatemp, DD.ARITH_MINUS, N_OP, aadd1);
    	aatemp = operateMany(aadd, aatemp, DD.ARITH_MINUS, N_OP, aadd2);
    	int aares = operateMany(aadd, aatemp, DD.ARITH_SUM,N_OP, aadd1);
    	    	
//    	DD ldd = new LOGAADD(alOrder);
//    	int ldd2 = ldd.buildDDFromOrderedTree(buildTestTree(type), var2ID);
//    	int ldd1 = ldd.buildDDFromOrderedTree(buildTestTree(type+1), var2ID);
//    	int ltemp = operateMany(ldd, ldd1, DD.ARITH_SUM, N_OP, ldd2);
//    	ltemp = operateMany(ldd, ltemp, DD.ARITH_MINUS, N_OP, ldd1);
//    	ltemp = operateMany(ldd, ltemp, DD.ARITH_MINUS, N_OP, ldd2);
//    	int lres = operateMany(ldd, ltemp, DD.ARITH_SUM,N_OP, ldd1);
    	
    	if (print){
    		Graph g1 = add.getGraph(ares);
        	g1.launchViewer(1300, 770);
        	Graph g2= aadd.getGraph(aares);
        	g2.launchViewer(1300, 770);
//        	Graph g3 = ldd.getGraph(lres);
//        	g3.launchViewer(1300, 770);
    	}
    	
    	//Evaluates each possible assignation.  still done manual
    	//*TODO Change to it depends on the tree, rather than manually change
    	ArrayList asgn = new ArrayList(); 	
    	double max_aadiff = 0.0;
    	double max_ldiff = 0.0;
    	for (int i = 0; i < 1<<N_var; i++){
    		asgn.clear();
    		for (int j = 0; j < N_var; j++){
    			asgn.add(toBool(((i >> j)) % 2));
    		}
    		System.out.println(asgn);
    		double adds = add.evaluate(ares, asgn);
    		double aadds = aadd.evaluate(aares, asgn);
    		
    		double aadiff = Math.abs(adds - aadds);
    		
    		double n_aadiff = aadiff/adds;
    		
    		
    		if (Math.abs(adds)>0.0 && n_aadiff > max_aadiff) max_aadiff = n_aadiff;
    	}	
    	System.out.println("MAX_aadiff: "+max_aadiff);
    	System.out.println("MAX_ldiff: "+max_ldiff);
    }
    
    public static void errorTest2(int type, Boolean print,int N_OP){
    	buildOrder();
    	DD add = new ADD(alOrder); 	
    	int add1 = add.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int add2 = add.getConstantNode(1.0);
    	int ares = operateMany(add, add1, DD.ARITH_SUM, N_OP, add2);
    	
    	DD aadd = new AADD(alOrder); 	
    	int aadd1 = aadd.buildDDFromOrderedTree(buildTestTree(type), var2ID);
    	int aadd2 = aadd.getConstantNode(1.0);
    	int aares = operateMany(aadd, aadd1, DD.ARITH_SUM, N_OP, aadd2);    	    	
    	
    	if (print){
    		Graph g1 = add.getGraph(ares);
        	g1.launchViewer(1300, 770);
        	Graph g2= aadd.getGraph(aares);
        	g2.launchViewer(1300, 770);
        }
    	
    	//Evaluates each possible assignation.  still done manual
    	//*TODO Change to it depends on the tree, rather than manually change
    	ArrayList asgn = new ArrayList(); 	
    	double max_aadiff = 0.0;
    	
    	
    	for (int i = 0; i < 1<<N_var; i++){
    		asgn.clear();
    		for (int j = 0; j < N_var; j++){
    			asgn.add(toBool(((i >> j)) % 2));
    		}
    		System.out.println(asgn);
    		double adds = add.evaluate(ares, asgn);
    		double aadds = aadd.evaluate(aares, asgn);
    		
    		double aadiff = Math.abs(adds - aadds);
    		
    		double n_aadiff = aadiff/adds;
    		
    		
    		if (Math.abs(adds)>0.0 && n_aadiff > max_aadiff) max_aadiff = n_aadiff;
    	}	
    	System.out.println("MAX_aadiff: "+max_aadiff);
    }

    
    public static Boolean toBool(int i) {
    	return (i == 1);
    }
    
    //Applies and Reapplies an operation to a given node.  Returns the final node.
    public static int operateMany(DD context, int topNode, int op, int numOps, int tgt){
    	int temp = topNode;
    	for (int i = 0; i < numOps; i++){
    		temp = context.applyInt(temp, tgt, op);
    	}
    	return temp;
    }
    
    // Efficient (log2) version of the above.
//    public static int operateManyEff(DD context, int topNode, int op, int numOps){
//    	if (numOps==1) return topNode;
//    	if (numOps==2) return context.applyInt(topNode, topNode, op);
//    	int temp = operateManyEff(context, topNode, op, numOps/2);
//		temp = context.applyInt(temp, temp, op);
//    	if (numOps%2 == 1) temp = context.applyInt(topNode, temp, op);
//    	return temp;
//    }
}
