package logic.add_gen;

import java.text.DecimalFormat;

public abstract class Gen implements Comparable{
	
	public static final double EPS = 1e-10;  
//	public static final double EPS = 1.23259516440783e-32;  /* = 2^-106 */
//	public static final double EPS = 6.6174449004242214e-24;  /* = 2^-77 */
//	public static final double EPS = 1.1102230246251565e-16;  /* = 2^-53 */
//	public static final double EPS = 1.4901161193847656e-08;  /* = 2^-26 */
	
	public Gen() {
	};
	public Gen (double d) {
	};
	
	public abstract Gen add(Gen x);
	
	public Gen minus(Gen y)	{
		if (isNaN()) return this;
		return add(y.negate());
	}

	
	public abstract Gen multiply(Gen x);
	public abstract Gen divide(Gen x);
	public abstract Gen negate();
	
	public abstract Gen sqrt();
	public abstract Gen abs();
	public abstract boolean isNaN();
	
	public abstract double value();
	public abstract Gen valueOf(double d);
	public abstract boolean equals(Gen y);
	public abstract int compareTo(Object x);
	public abstract Long toRawLongBits();
	public abstract String toString();
//	#printing
	public static DecimalFormat _df = new DecimalFormat("#.###");
	
	public Gen pow(int exp)
	{
		if (exp == 0.0)
			return valueOf(1.0);
		Gen s = valueOf(1.0);
		Gen r = valueOf(1.0).multiply(this);
		
		int n = Math.abs(exp);
		if (n > 1) {
			/* Use binary exponentiation */
		    while (n > 0) {
		        if (n % 2 == 1) {
		        	s = s.multiply(r);
		        }
		        n /= 2;
		        if (n > 0) r = r.multiply(r);
		    }
		} else {
		    s = r;
		}
		/* Compute the reciprocal if n is negative. */
		if (exp < 0)
			return s.reciprocal();
		return s;
	}
	
	public int sign() {
		if (this.value()>0) return 1;
		if (this.value()<0) return -1;
		return 0;
	}
	
	public boolean isZero() {
		return (this.abs().value()<EPS); 
	}
	
	public Gen max(Gen x) {
		if (ge(x)) return this;
		else return x;
	}
	
	public Gen min(Gen x) {
		if (this.compareTo(x)>0) return x;
		else return this;
	}
	
	public Gen reciprocal()
	{
		return valueOf(1.0).divide(this);
	}
	
	public Object clone()
	{
		try {
			return super.clone();
		}
		catch (CloneNotSupportedException ex) {
			// should never reach here
			return null;
		}
	}

	/**
	 * Tests whether this value is greater than another <tt>SimpleDouble</tt> value.
	 * @param y a SimpleDouble value
	 * @return true if this value > y
	 */
	public boolean gt(Gen y)
	{
		return (compareTo(y) > 0);
	}
	/**
	 * Tests whether this value is greater than or equals to another <tt>SimpleDouble</tt> value.
	 * @param y a SimpleDouble value
	 * @return true if this value >= y
	 */
	public boolean ge(Gen y)
	{
		return (compareTo(y) >= 0);
	}
	/**
	 * Tests whether this value is less than another <tt>SimpleDouble</tt> value.
	 * @param y a SimpleDouble value
	 * @return true if this value < y
	 */
	public boolean lt(Gen y)
	{
		return (compareTo(y)<0);
	}
	/**
	 * Tests whether this value is less than or equal to another <tt>SimpleDouble</tt> value.
	 * @param y a SimpleDouble value
	 * @return true if this value <= y
	 */
	public boolean le(Gen y){
		return (compareTo(y)<=0);
	}

	
	public int round(long x){
		return (int)(  (x + ((long)1<<31) )>>32);
	}
	
	public int hashCode() {
		long bits = this.toRawLongBits();
		int sbits = round(bits);
		return sbits;
	}
}
