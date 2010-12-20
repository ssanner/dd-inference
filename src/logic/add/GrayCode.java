//////////////////////////////////////////////////////////////////////
//
// Algebraic Decision Diagram Package (Gray/Binary code conversion)
//
// Author: Scott Sanner (ssanner@cs.toronto.edu)
// Date:   7/25/03
//
//////////////////////////////////////////////////////////////////////

package logic.add;

/**
 * General class for implementation of AADD data structure
 **/
public class GrayCode {

    // Constants
    public static final int  INT_HIGH_BIT  = 1 << 31;
    public static final long LONG_HIGH_BIT = 1 << 63;

    // Conversion functions
    public static int Binary2Gray(int b) {
	return (b & INT_HIGH_BIT) + (b ^ (b >> 1));
    }

    public static int Gray2Binary(int g) {
	int b = (g & INT_HIGH_BIT);
	for (int i = 30; i >= 0; i--) {
	    b += ((((b >> 1) ^ g) & (1 << i)) != 0) ? (1 << i) : 0;
	}
	return b;
    }

    public static long Binary2Gray(long b) {
	return (b & LONG_HIGH_BIT) + (b ^ (b >> 1));
    }

    public static long Gray2Binary(long g) {
	long b = (g & LONG_HIGH_BIT);
	for (int i = 62; i >= 0; i--) {
	    b += ((((b >> 1) ^ g) & (1l << i)) != 0) ? (1l << i) : 0;
	}
	return b;
    }

    // Testing function
    public static void main(String args[]) {
	
	int nums = 10000000;

	for (int b=0; b<=100; b++) {
	    int g = Binary2Gray(b);
	    int b2 = Gray2Binary(g);
	    System.out.println("B:" + b + "   G:" + g + "   " + (b == b2));
	}
	
	System.out.println("Checking " + nums + " gray code int conversions...");
	for (int b1=0; b1<=nums; b1++) {
	    if ((b1 % 1000000) == 0) {
		System.out.println("  - " + b1 + "..." + (b1 + 1000000));
	    }
	    int g = Binary2Gray(b1);
	    int b2 = Gray2Binary(g);
	    if (b1 != b2) {
		System.out.println("Error: " + b1 + "/" + b2);
	    }
	}

	System.out.println("Checking highest bits " + nums + " gray code int conversion...");
	int highest_int = (int)((1l<<32)-1);
	for (int b3=highest_int; b3>=(highest_int - nums); b3--) {
	    if ((b3 % 1000000) == 0) {
		System.out.println("  - " + b3 + "..." + (b3 - 1000000));
	    }
	    int g = Binary2Gray(b3);
	    int b2 = Gray2Binary(g);
	    if (b3 != b2) {
		System.out.println("Error: " + b3 + "/" + b2);
	    }
	}

	System.out.println("Checking " + nums + " gray code long conversions...");
	for (long l=0; l<=nums; l++) {
	    if ((l % 1000000) == 0) {
		System.out.println("  - " + l + "..." + (l + 1000000));
	    }
	    long g = Binary2Gray(l);
	    long b2 = Gray2Binary(g);
	    if (l != b2) {
		System.out.println("Error: " + l + "/" + b2);
	    }
	}

	System.out.println("Checking highest bits " + nums + " gray code long conversion...");
	long highest_long = (1l<<63) + ((1l<<63)-1);
	for (long l3=highest_long; l3>=(highest_int - nums); l3--) {
	    if ((l3 % 1000000) == 0) {
		System.out.println("  - " + l3 + "..." + (l3 - 1000000));
	    }
	    long g = Binary2Gray(l3);
	    long b2 = Gray2Binary(g);
	    if (l3 != b2) {
		System.out.println("Error: " + l3 + "/" + b2);
	    }
	}
    }
}
    
