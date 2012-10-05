package logic.add_gen;

import java.io.*;

public class SimpleDouble extends Gen implements Serializable, Comparable, Cloneable{
	public static final SimpleDouble NaN = new SimpleDouble(Double.NaN);
		
	@Override
	public SimpleDouble valueOf(double x) { return new SimpleDouble(x); }
	
	/*** The value of SimpleDouble.*/
	private double _val;
	
	/** Creates a new SimpleDouble with value 0.0. */
	public SimpleDouble(){
		_val = 0.0;
	}
	
	/**Creates a new SimpleDouble with value x.*/
	public SimpleDouble(double x){
		_val = x;
	}
	
	/**
	 * Creates a new SimpleDouble with value equal to the argument.
	 * 
	 * @param sd the value to initialize
	 */
	public SimpleDouble(SimpleDouble sd){
		_val = sd._val;
	}
	
	/**
	 * Returns a SimpleDouble whose value is <tt>(this + y)</tt>.
	 * 
	 * @param y the addend
	 * @return <tt>(this + y)</tt>
	 */	
	@Override
	public Gen add(Gen alg_y){
		SimpleDouble y = (SimpleDouble) alg_y;
		return (Gen) (new SimpleDouble(this)).selfAdd(y);
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
	private SimpleDouble selfAdd(SimpleDouble y){
		_val += y._val;
		return this;
	}
			
	/**
	 * Returns a SimpleDouble whose value is <tt>-this</tt>.
	 * 
	 * @return <tt>-this</tt>
	 */
	@Override
	public Gen negate()
	{
		if (isNaN()) return this;
		return new SimpleDouble(-_val);
	}
	
	/**
	 * Returns a SimpleDouble whose value is <tt>(this * y)</tt>.
	 * 
	 * @param y the multiplicand
	 * @return <tt>(this * y)</tt>
	 */
	@Override
	public Gen multiply(Gen y)
	{
		if (isNaN()) return this;
		if (y.isNaN()) return y;
	  return (new SimpleDouble(this)).selfMultiply((SimpleDouble) y);
	}
	
	/**
	 * Multiplies this by the argument, returning this.
	 * To prevent altering constants, 
	 * this method <b>must only</b> be used on values known to 
	 * be newly created. 
	 * 
	 * @param y a SimpleDouble value to multiply by
	 * @return this
	 */
	private SimpleDouble selfMultiply(SimpleDouble y)
	{
		_val*=y._val;
		return this;
	}
	
	/**
	 * Returns a SimpleDouble whose value is <tt>(this / y)</tt>.
	 * 
	 * @param y the divisor
	 * @return <tt>(this / y)</tt>
	 */
	@Override
	public Gen divide(Gen alg_y)
	{
		return new SimpleDouble(_val/((SimpleDouble) alg_y)._val);
	}

	/**
	 * Converts this value to the nearest double-precision number.
	 * 
	 * @return the nearest double-precision number to this value
	 */
	@Override
	public double value()
	{
		return _val;
	}

	/**
	 * Tests whether this value is NaN.
	 * 
	 * @return true if this value is NaN
	 */
	@Override
	public boolean isNaN() { return Double.isNaN(_val); }
	
	/**
	 * Tests whether this value is equal to another <tt>SimpleDouble</tt> value.
	 * 
	 * @param y a SimpleDouble value
	 * @return true if this value = y
	 */
	@Override
	public boolean equals(Gen alg_y){
		SimpleDouble y = (SimpleDouble) alg_y;
		return Math.abs(_val - y._val)<EPS;
	}
	
	/**
	 * Compares two SimpleDouble objects numerically.
	 * 
	 * @return -1,0 or 1 depending on whether this value is less than, equal to
	 * or greater than the value of <tt>o</tt>
	 */
	@Override
	public int compareTo(Object o) {
	    SimpleDouble other = (SimpleDouble) o;
	    if (_val > other._val) return 1;
	    if (_val < other._val) return -1;
	    return 0;
	}
	
	public String toString()
	{
		return _df.format(_val);
	}
				
	public SimpleDouble abs(){
		return new SimpleDouble(Math.abs(_val));
	}

	@Override
	public Gen sqrt() {
		return new SimpleDouble(Math.sqrt(_val) );
	}
	
	@Override
	public Long toRawLongBits() {
		return Double.doubleToLongBits(this._val);
	}

}