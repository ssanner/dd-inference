package logic.add_gen;

import java.io.*;
import util.NumericalUtils;

public class LogDouble extends Gen implements Serializable, Comparable, Cloneable{
	public static final LogDouble NaN = new LogDouble(Double.NaN,false);
		
	@Override
	public LogDouble valueOf(double x) { return new LogDouble(x); }
	
	/*** The value of LogDouble.*/
	private double _logVal;
	private boolean _neg;
	
	/** Creates a new LogDouble with value 0.0. */
	public LogDouble(){
		_logVal = 0.0;
		_neg = false;
	}
	
	/**Creates a new LogDouble with value x.*/
	public LogDouble(double x){
		_neg = false;
		if (x<0){
			_neg = true;
			x = -x;
		}
		_logVal = Math.log(x);
	}
	
	public LogDouble(double x, boolean n){
		_logVal = x;
		_neg = n;
	}
	
	/**
	 * Creates a new LogDouble with value equal to the argument.
	 * 
	 * @param sd the value to initialize
	 */
	public LogDouble(LogDouble sd){
		_logVal = sd._logVal;
		_neg = sd._neg;
	}
	
	/**
	 * Returns a LogDouble whose value is <tt>(this + y)</tt>.
	 * 
	 * @param y the addend
	 * @return <tt>(this + y)</tt>
	 */	
	@Override
	public Gen add(Gen alg_y){
		LogDouble y = (LogDouble) alg_y;
		return (Gen) (new LogDouble(this)).selfAdd(y);
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
	private LogDouble selfAdd(LogDouble y){
		if ( (!_neg && !y._neg) || (_neg && y._neg) ) {
			_logVal = NumericalUtils.LogSum(_logVal, y._logVal);
		}
		else {
			if (_logVal > y._logVal) _logVal = NumericalUtils.LogMinus(_logVal, y._logVal);
			else {
				_logVal = NumericalUtils.LogMinus(y._logVal,_logVal);
				_neg = !_neg;//==y._neg
			}
		}
		return this;
	}
			
	/**
	 * Returns a LogDouble whose value is <tt>-this</tt>.
	 * 
	 * @return <tt>-this</tt>
	 */
	@Override
	public Gen negate()
	{
		if (isNaN()) return this;
		return new LogDouble(_logVal,!_neg);
	}
	
	/**
	 * Returns a LogDouble whose value is <tt>(this * y)</tt>.
	 * 
	 * @param y the multiplicand
	 * @return <tt>(this * y)</tt>
	 */
	@Override
	public Gen multiply(Gen y)
	{
		if (isNaN()) return this;
		if (y.isNaN()) return y;
	  return (new LogDouble(this)).selfMultiply((LogDouble) y);
	}
	
	/**
	 * Multiplies this by the argument, returning this.
	 * To prevent altering constants, 
	 * this method <b>must only</b> be used on values known to 
	 * be newly created. 
	 * 
	 * @param y a LogDouble value to multiply by
	 * @return this
	 */
	private LogDouble selfMultiply(LogDouble y)
	{
		_logVal += y._logVal;
		_neg = (_neg && !y._neg) || (!_neg && y._neg);  
		return this;
	}
	
	/**
	 * Returns a LogDouble whose value is <tt>(this / y)</tt>.
	 * 
	 * @param y the divisor
	 * @return <tt>(this / y)</tt>
	 */
	@Override
	public Gen divide(Gen alg_y)
	{
		return new LogDouble(this).selfDivide((LogDouble) alg_y);
	}

	private LogDouble selfDivide(LogDouble y)
	{
		_logVal -= y._logVal;
		_neg = (_neg && !y._neg) || (!_neg && y._neg);  
		return this;
	}
	
	/**
	 * Converts this value to the nearest double-precision number.
	 * 
	 * @return the nearest double-precision number to this value
	 */
	@Override
	public double value(){
		return (_neg?-1:1)*Math.exp(_logVal);
	}

	/**
	 * Tests whether this value is NaN.
	 * 
	 * @return true if this value is NaN
	 */
	@Override
	public boolean isNaN() { return Double.isNaN(_logVal); }
	/**
	 * Tests whether this value is equal to another <tt>LogDouble</tt> value.
	 * 
	 * @param y a LogDouble value
	 * @return true if this value = y
	 */
	@Override
	public boolean equals(Gen alg_y){
		LogDouble dif = (LogDouble) this.minus(alg_y);
		if (dif.isZero()) return true;
		else return false;
//		LogDouble y = (LogDouble) alg_y;
//		if (alg_y.isZero()) return this.isZero();
//		if (_neg != y._neg) return false;		
//		if (_logVal == y._logVal) return true;
//		return Math.abs(_logVal - y._logVal) < EPS;
	}
	
	/**
	 * Compares two LogDouble objects numerically.
	 * 
	 * @return -1,0 or 1 depending on whether this value is less than, equal to
	 * or greater than the value of <tt>o</tt>
	 */
	@Override
	public int compareTo(Object o) {
	    LogDouble other = (LogDouble) o;
	    if (_neg){
	    	if (!other._neg) return -1;
	    	if (_logVal < other._logVal) return 1;
		    if (_logVal > other._logVal) return -1;
	    }
	    else {
	    	if (other._neg) return 1;
	    	if (_logVal > other._logVal) return 1;
	    	if (_logVal < other._logVal) return -1;
	    }
	    return 0;
	}
	
	public String toString()
	{
		return _df.format(value());
	}
		
	public LogDouble abs(){
		return new LogDouble(_logVal,false);
	}

	@Override
	public Gen sqrt() {
		if (_neg) System.err.println("Sqrt of negative Num!");
		return new LogDouble(_logVal/2.0,false);
	}
	
	@Override
	public Long toRawLongBits() {
		// TODO Auto-generated method stub
		long l = Double.doubleToLongBits(_logVal) ;
	    return l;//( (long) (_neg?1:0)) + l;
		
	}
}