/** Frequently used numerical utilities (e.g, log-sum-exp).
 *   
 * @author Scott Sanner (ssanner@gmail.com)
 */

package util;

import java.io.*;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

public class NumericalUtils {
	
	/* for a,b given log versions log_a, log_b returns log(a + b);
	 * also known as log-sum-exp
	 * 
	 * NOTE: code needs to be modified further if INF or -INF values
	 *       are expected.
	 */
	public static double LogSum(double log_a, double log_b) {
		if (log_a == Double.NEGATIVE_INFINITY) return log_b;
		if (log_b == Double.NEGATIVE_INFINITY) return log_a;
		
		double max = Math.max(log_a, log_b);
		double sum = Math.exp(log_a - max) + Math.exp(log_b - max);
		return Math.log(sum) + max;
	}
	
	public static double LogMinus(double log_a, double log_b) {
		if (log_b == log_a){
			return Double.NEGATIVE_INFINITY;
		}
		if (log_b > log_a){
			System.err.println("Impossible to make "+Math.log(-1));
			System.err.println("Impossible to make logMinus!");
			new Exception().printStackTrace(); 
			System.exit(17);
		}
		double sum = 1 - Math.exp(log_b - log_a); //always 0<sum<1
		return Math.log(sum) + log_a;
	}

	
	public static void main(String[] args) {
	
		// Test LogSum
		double a = 12d;
		double b = 1000d;
		double a_plus_b = a + b;
		double log_a = Math.log(a);
		double log_b = Math.log(b);
		double log_a_plus_b = LogSum(log_a, log_b);
		System.out.println("LogSum: " + a_plus_b + " == " + Math.exp(log_a_plus_b));
	}
}
