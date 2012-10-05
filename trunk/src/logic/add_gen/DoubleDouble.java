package logic.add_gen;

import java.io.*;

public class DoubleDouble extends Gen implements Serializable, Comparable, Cloneable{
	/**
	 * Immutable, extended-precision floating-point numbers 
	 * which maintain 106 bits (approximately 30 decimal digits) of precision. 
	 * <p>
	 * A DoubleDouble uses a representation containing two double-precision values.
	 * A number x is represented as a pair of doubles, x.hi and x.lo,
	 * such that the number represented by x is x.hi + x.lo, where
	 * <pre>
	 *    |x.lo| <= 0.5*ulp(x.hi)
	 * </pre>
	 * and ulp(y) means "unit in the last place of y".  
	 * The basic arithmetic operations are implemented using 
	 * convenient properties of IEEE-754 floating-point arithmetic.
	 * <p>
	 * The range of values which can be represented is the same as in IEEE-754.  
	 * The precision of the representable numbers 
	 * is twice as great as IEEE-754 double precision.
	 * <p>
	 * The correctness of the arithmetic algorithms relies on operations
	 * being performed with standard IEEE-754 double precision and rounding.
	 * This is the Java standard arithmetic model, but for performance reasons 
	 * Java implementations are not
	 * constrained to using this standard by default.  
	 * Some processors (notably the Intel Pentium architecure) perform
	 * floating point operations in (non-IEEE-754-standard) extended-precision.
	 * A JVM implementation may choose to use the non-standard extended-precision
	 * as its default arithmetic mode.
	 * To prevent this from happening, this code uses the
	 * Java <tt>strictfp</tt> modifier, 
	 * which forces all operations to take place in the standard IEEE-754 rounding model. 
	 * <p>
	 * The API provides a value-oriented interface.  DoubleDouble values are 
	 * immutable; operations on them return new objects carrying the result
	 * of the operation.  This provides a much simpler semantics for
	 * writing DoubleDouble expressions, and Java memory management is efficient enough that 
	 * this imposes very little performance penalty.
	 * <p>
	 * This implementation uses algorithms originally designed variously by Knuth, Kahan, Dekker, and
	 * Linnainmaa.  Douglas Priest developed the first C implementation of these techniques. 
	 * Other more recent C++ implementation are due to Keith M. Briggs and David Bailey et al.
	 * 
	 * <h3>References</h3>
	 * <ul>
	 * <li>Priest, D., <i>Algorithms for Arbitrary Precision Floating Point Arithmetic</i>,
	 * in P. Kornerup and D. Matula, Eds., Proc. 10th Symposium on Computer Arithmetic, 
	 * IEEE Computer Society Press, Los Alamitos, Calif., 1991.
	 * <li>Yozo Hida, Xiaoye S. Li and David H. Bailey, 
	 * <i>Quad-Double Arithmetic: Algorithms, Implementation, and Application</i>, 
	 * manuscript, Oct 2000; Lawrence Berkeley National Laboratory Report BNL-46996.
	 * <li>David Bailey, <i>High Precision Software Directory</i>; 
	 * <tt>http://crd.lbl.gov/~dhbailey/mpdist/index.html</tt>
	 * </ul>
	 * 
	 * 
	 * @author Martin Davis
	 *
	 */

	/**
	 * A value representing the result of an operation which does not return a valid number.
	 */
	public static final DoubleDouble NaN = new DoubleDouble(Double.NaN, Double.NaN);
	
	/**
	 * Converts the string argument to a DoubleDouble number.
	 * 
	 * @param str a string containing a representation of a numeric value
	 * @return the extended precision version of the value
	 * @throws NumberFormatException if <tt>s</tt> is not a valid representation of a number
	 */
	/**
	 * Converts the <tt>double</tt> argument to a DoubleDouble number.
	 * 
	 * @param x a numeric value
	 * @return the extended precision version of the value
	 */
	@Override
	public DoubleDouble valueOf(double x) { return new DoubleDouble(x); }
	
	/**
	 * The value to split a double-precision value on during multiplication
	 */
	private static final double SPLIT = 134217729.0D; // 2^27+1, for IEEE double
	
	/**
	 * The high-order component of the double-double precision value.
	 */
	private double hi = 0.0;
	
	/**
	 * The low-order component of the double-double precision value.
	 */
	private double lo = 0.0;
	
	/**
	 * Creates a new DoubleDouble with value 0.0.
	 */
	public DoubleDouble()
	{
		init(0.0);
	}
		
	/**
	 * Creates a new DoubleDouble with value x.
	 * 
	 * @param x the value to initialize
	 */
	public DoubleDouble(double x)
	{
		init(x);
	}
	
	/**
	 * Creates a new DoubleDouble with value (hi, lo).
	 * 
	 * @param hi the high-order component 
	 * @param lo the high-order component 
	 */
	public DoubleDouble(double hi, double lo)
	{
		init(hi, lo);
	}
		
	/**
	 * Creates a new DoubleDouble with value equal to the argument.
	 * 
	 * @param dd the value to initialize
	 */
	public DoubleDouble(DoubleDouble dd)
	{
		init(dd);
	}
	
	private void init(double x)
	{
		init(x, 0.0);
	}
	
	private void init(double hi, double lo)
	{
		this.hi = hi;
		this.lo = lo;		
	}
	
	private void init(DoubleDouble dd)
	{
		init(dd.hi, dd.lo);	
	}
		
	/**
	 * Returns a DoubleDouble whose value is <tt>(this + y)</tt>.
	 * 
	 * @param y the addend
	 * @return <tt>(this + y)</tt>
	 */	
	@Override
	public Gen add(Gen alg_y)
	{
		DoubleDouble y = (DoubleDouble) alg_y;
		if (isNaN()) return (Gen) this;
		return (Gen) (new DoubleDouble(this)).selfAdd(y);
	}
		
	/**
	 * Adds the argument to the value of <tt>this</tt>.
	 * To prevent altering constants, 
	 * this method <b>must only</b> be used on values known to 
	 * be newly created. 
	 * 
	 * @param y the addend
	 * @return <tt>this</tt>, with its value incremented by <tt>y</tt>
	 */
	private DoubleDouble selfAdd(DoubleDouble y)
	{
		double H, h, T, t, S, s, e, f;
	  	S = hi + y.hi; 
	  	T = lo + y.lo; 
	  	e = S - hi; 
	  	f = T - lo; 
	  	s = S-e; 
	  	t = T-f; 
	  	s = (y.hi-e)+(hi-s); 
	  	t = (y.lo-f)+(lo-t); 
	  	e = s+T; H = S+e; h = e+(S-H); e = t+h;
	  
	  	double zhi = H + e;
	  	double zlo = e + (H - zhi);
	  	hi = zhi;
	  	lo = zlo;
	  	
	  	return this;
	}
		
	/**
	 * Returns a DoubleDouble whose value is <tt>-this</tt>.
	 * 
	 * @return <tt>-this</tt>
	 */
	@Override
	public Gen negate()
	{
		if (isNaN()) return this;
		return new DoubleDouble(-hi, -lo);
	}
		
	/**
	 * Returns a DoubleDouble whose value is <tt>(this * y)</tt>.
	 * 
	 * @param y the multiplicand
	 * @return <tt>(this * y)</tt>
	 */
	@Override
	public Gen multiply(Gen y)
	{
		if (isNaN()) return this;
		if (y.isNaN()) return y;
	  return (new DoubleDouble(this)).selfMultiply((DoubleDouble) y);
	}
		
	/**
	 * Multiplies this by the argument, returning this.
	 * To prevent altering constants, 
	 * this method <b>must only</b> be used on values known to 
	 * be newly created. 
	 * 
	 * @param y a DoubleDouble value to multiply by
	 * @return this
	 */
	private DoubleDouble selfMultiply(DoubleDouble y)
	{
	  double hx, tx, hy, ty, C, c;
	  C = SPLIT * hi; hx = C-hi; c = SPLIT * y.hi;
	  hx = C-hx; tx = hi-hx; hy = c-y.hi; 
	  C = hi*y.hi; hy = c-hy; ty = y.hi-hy;
	  c = ((((hx*hy-C)+hx*ty)+tx*hy)+tx*ty)+(hi*y.lo+lo*y.hi);
	  double zhi = C+c; hx = C-zhi; 
	  double zlo = c+hx;
	  hi = zhi;
	  lo = zlo;
	  return this;
	}
		
	/**
	 * Returns a DoubleDouble whose value is <tt>(this / y)</tt>.
	 * 
	 * @param y the divisor
	 * @return <tt>(this / y)</tt>
	 */
	@Override
	public Gen divide(Gen alg_y)
	{
	  DoubleDouble y = (DoubleDouble) alg_y;
	  double hc, tc, hy, ty, C, c, U, u;
	  C = hi/y.hi; c = SPLIT*C; hc =c-C;  u = SPLIT*y.hi; hc = c-hc;
	  tc = C-hc; hy = u-y.hi; U = C * y.hi; hy = u-hy; ty = y.hi-hy;
	  u = (((hc*hy-U)+hc*ty)+tc*hy)+tc*ty;
	  c = ((((hi-U)-u)+lo)-C*y.lo)/y.hi;
	  u = C+c; 
	  
	  double zhi = u; 
	  double zlo = (C-u)+c;
	  return new DoubleDouble(zhi, zlo);
	}

	/**
	 * Returns a DoubleDouble whose value is  <tt>1 / this</tt>.
	 * 
	 * @return the reciprocal of this value
	 */
	@Override		
	public Gen reciprocal()
	{
	  double  hc, tc, hy, ty, C, c, U, u;
	  C = 1.0/hi; 
	  c = SPLIT*C; 
	  hc =c-C;  
	  u = SPLIT*hi;
	  hc = c-hc; tc = C-hc; hy = u-hi; U = C*hi; hy = u-hy; ty = hi-hy;
	  u = (((hc*hy-U)+hc*ty)+tc*hy)+tc*ty;
	  c = ((((1.0-U)-u))-C*lo)/hi;
	  
	  double  zhi = C+c; 
	  double  zlo = (C-zhi)+c;
	  return new DoubleDouble(zhi, zlo);
	}
		
	/**
	 * Converts this value to the nearest double-precision number.
	 * 
	 * @return the nearest double-precision number to this value
	 */
	@Override
	public double value()
	{
		return hi + lo;
	}

	/**
	 * Tests whether this value is NaN.
	 * 
	 * @return true if this value is NaN
	 */
	@Override
	public boolean isNaN() { return Double.isNaN(hi); }
		
	/**
	 * Tests whether this value is equal to another <tt>DoubleDouble</tt> value.
	 * 
	 * @param y a DoubleDouble value
	 * @return true if this value = y
	 */
	@Override
	public boolean equals(Gen alg_y)
	{
		DoubleDouble y = (DoubleDouble) alg_y;
		return Math.abs(hi - y.hi)<EPS && Math.abs(lo - y.lo)<EPS;
	}
		
	/**
	 * Compares two DoubleDouble objects numerically.
	 * 
	 * @return -1,0 or 1 depending on whether this value is less than, equal to
	 * or greater than the value of <tt>o</tt>
	 */
	@Override
	public int compareTo(Object o) {
		DoubleDouble other = (DoubleDouble) o;

	    if (hi < other.hi) return -1;
	    if (hi > other.hi) return 1;
	    if (lo < other.lo) return -1;
	    if (lo > other.lo) return 1;
	    return 0;
	}
		
		
	/*------------------------------------------------------------
	 *   Output
	 *------------------------------------------------------------
	 */
	
	/**
	 * Dumps the components of this number to a string.
	 * 
	 * @return a string showing the components of the number
	 */
	public String dump()
	{
		return "DD<" + hi + ", " + lo + ">";
	}
	
	/**
	 * Returns a string representation of this number, in either standard or scientific notation.
	 * If the magnitude of the number is in the range [ 10<sup>-3</sup>, 10<sup>8</sup> ]
	 * standard notation will be used.  Otherwise, scientific notation will be used.
	 * 
	 * @return a string representation of this number
	 */
	public String toString()
	{
		return _df.format(hi);
	}
	
	@Override
	public Gen abs()
	{
		if (isNaN()) return NaN;
		if (this.hi<0|| (this.hi==0&&this.lo<0))
			return (DoubleDouble) negate();
		return new DoubleDouble(this);
	}

	@Override
	public Gen sqrt() {
	  /* Strategy:  Use Karp's trick:  if x is an approximation
    to sqrt(a), then
       sqrt(a) = a*x + [a - (a*x)^2] * x / 2   (approx)
    The approximation is accurate to twice the accuracy of x.
    Also, the multiplication (a*x) and [-]*x can be done with
    only half the precision.
 */
		if (this.hi==0 && this.lo==0)
	    return new DoubleDouble(0.0);

	  if (this.hi<0 || (this.hi==0 && this.lo<0)) {
	    return NaN;
	  }

	  double x = 1.0 / Math.sqrt(hi);
	  double ax = hi * x;
	  
	  DoubleDouble axdd = new DoubleDouble(ax);
	  DoubleDouble diffSq = (DoubleDouble) this.minus(axdd.multiply(axdd));
	  double d2 = diffSq.hi * (x * 0.5);
	  
	  return axdd.add(new DoubleDouble(d2));
	}


	@Override
	public Long toRawLongBits() {
		return Double.doubleToLongBits( this.hi+this.lo);
	}
}
