package logic.add_gen;

import java.util.*;

public class SAINodeIndex 
  implements Comparable {

    public int _nGid;
    public int _nID1;
    public int _nID2;
    
    public Gen _aOffset1;
    public Gen _aMult1;
    public Gen _aOffset2;
    public Gen _aMult2;
    public Gen _aDistance;
    public int _iHashType = 0;
    
    private int offset = 0;

    public static final boolean USE_GRAY_CODE = false;
    public static final boolean ROUND = true;

    public static final int SHIFT_BITS = 8;

    public SAINodeIndex(int gid, int low, int high,
			Gen o_l, Gen m_l, Gen o_h, Gen m_h) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_aOffset1  = o_l;
	_aMult1    = m_l;
	_aOffset2  = o_h;
	_aMult2    = m_h;
	_aDistance = ( o_l.multiply(o_l).add(
				   o_h.multiply(o_h).add( 
				   m_l.multiply(m_l).add(
				   m_h.multiply(m_h)) ) )
				   ).sqrt();
    }
    
    public SAINodeIndex(int gid, int low, int high,
			Gen o_l, Gen m_l, Gen o_h, Gen m_h,
			Gen perturb) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_aOffset1  = o_l;
	_aMult1    = m_l;
	_aOffset2 = o_h;
	_aMult2   = m_h;
	_aDistance = ( o_l.multiply(o_l).add(
			   o_h.multiply(o_h).add( 
			   m_l.multiply(m_l).add(
			   m_h.multiply(m_h)) ) )
			   ).sqrt().add(perturb);
    }

    public SAINodeIndex(int gid, int low, int high,
			Gen o_l, Gen m_l, Gen o_h, Gen m_h,
			int hashType) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_aOffset1  = o_l;
	_aMult1    = m_l;
	_aOffset2 = o_h;
	_aMult2   = m_h;
	_aDistance = ( o_l.multiply(o_l).add(
			   o_h.multiply(o_h).add( 
			   m_l.multiply(m_l).add(
			   m_h.multiply(m_h)) ) )
			   ).sqrt();
	_iHashType = hashType;
	offset = 0;
    }

    
    public void set(int gid, int low, int high,
		    Gen o_l, Gen m_l, Gen o_h, Gen m_h) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_aOffset1  = o_l;
	_aMult1    = m_l;
	_aOffset2  = o_h;
	_aMult2    = m_h;
	_aDistance = ( o_l.multiply(o_l).add(
			   o_h.multiply(o_h).add( 
			   m_l.multiply(m_l).add(
			   m_h.multiply(m_h)) ) )
			   ).sqrt();
	offset = 0;
    }
    
    public void set(int gid, int low, int high,
		    Gen o_l, Gen m_l, Gen o_h, Gen m_h,
		    Gen perturb) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_aOffset1  = o_l;
	_aMult1    = m_l;
	_aOffset2 = o_h;
	_aMult2   = m_h;
	_aDistance = ( o_l.multiply(o_l).add(
			   o_h.multiply(o_h).add( 
			   m_l.multiply(m_l).add(
			   m_h.multiply(m_h)) ) )
			   ).sqrt().add(perturb);
	offset = 0;
    }
     
    public void set(int gid, int low, int high,
		    Gen o_l, Gen m_l, Gen o_h, Gen m_h,
		    int hashType) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_aOffset1  = o_l;
	_aMult1    = m_l;
	_aOffset2 = o_h;
	_aMult2   = m_h;
	_aDistance = ( o_l.multiply(o_l).add(
			   o_h.multiply(o_h).add( 
			   m_l.multiply(m_l).add(
			   m_h.multiply(m_h)) ) )
			   ).sqrt();
	_iHashType = hashType;
	offset = 0;
    }
    
    public int hashCode() {
    	int hc = (_nGid<<20) + (_nID1 <<10) + (_nID2 <<0);
    	switch(_iHashType){
    	case (AADD.USE_4D):{
    		long b1 = (_aOffset1.hashCode()+1)>>>SHIFT_BITS;
	    	int i1 = (int)(b1 ^ (b1 >> 32) );
	    	long b2 = (_aOffset2.hashCode()+1)>>>SHIFT_BITS;
	    	int i2 = (int)(b2 ^ (b2 >> 32) );
	    	long b3 = (_aMult1.hashCode()+1)>>>SHIFT_BITS;
	    	int i3 = (int)(b3 ^ (b3 >> 32) );
	    	long b4 = (_aMult2.hashCode()+1)>>>SHIFT_BITS;
	    	int i4 = (int)(b4 ^ (b4 >> 32) );
	    	hc += -(i1 +i2 -i3+i4);
			break;
	    }
    	
    	default:{ //USE_DHASH
	    	long d1;
	    	int  i1;
	    	d1 = (_aDistance.hashCode()+1) >>> SHIFT_BITS;
		    i1 = (int)(d1 ^ (d1 >> 32));
	    	hc += -i1;
	    	break;
    	}
	    }
	    return hc + offset;
    }
    
    public boolean equals(Object o) {
		SAINodeIndex s = (SAINodeIndex)o;
		return ((_nGid == s._nGid) && 
			(_nID1 == s._nID1) && 
			(_nID2 == s._nID2) &&
			(_aOffset1.equals(s._aOffset1)) &&
			(_aOffset2.equals(s._aOffset2)) &&
			(_aMult1.equals(s._aMult1)) &&
			(_aMult2.equals(s._aMult2)) );
    }

    public int compareTo(Object o) {

		SAINodeIndex s = (SAINodeIndex)o;
		// Check for ID inequality
		if (this._nGid < s._nGid) {
		    return (-1);
		} else if (this._nGid > s._nGid) {
		    return (1);
		}
	
		if (this._nID1 < s._nID1) {
		    return (-1);
		} else if (this._nID1 > s._nID1) {
		    return (1);
		}

		if (this._nID2 < s._nID2) {
		    return (-1);
		} else if (this._nID2 > s._nID2) {
		    return (1);
		}

		// Return relative distance from origin - unless equal which
		// requires further checking.
		if (this._aDistance.lt(s._aDistance)) {
			return (-1);
		} else if (this._aDistance.gt(s._aDistance)) {
			return (1);
		}
		 
		// Now check for equivalence within precision!
		if (this.equals(o)) {
			return (0);
		}

		// Now perform standard ordered check
		if (this._aOffset1.value() <  s._aOffset1.value()) {
			return (-1);
		} else if (this._aOffset1.value() > s._aOffset1.value()) {
			return (1);
		}

		if (this._aMult1.value() < s._aMult1.value()) {
		   return (-1);
		} else if (this._aMult1.value() > s._aMult1.value()) {
		    return (1);
		}

		if (this._aOffset2.value() < s._aOffset2.value()) {
		    return (-1);
		} else if (this._aOffset2.value() > s._aOffset2.value()) {
		    return (1);
		}

		if (this._aMult2.value() < s._aMult2.value()) {
		    return (-1);
		} else if (this._aMult2.value() > s._aMult2.value()) {
		    return (1);
		}	

		System.out.println("ERROR: SAINodeIndex.compareTo(): Should not get here!");
		System.out.println(this + "\n" + s);
		Object o1 = null; o1.toString();
		return (0);
    }

    public String toString() {
	return "\n<" + _nGid + ", " + _nID1 + ", " + _nID2 + ", *" + _aDistance + "*, " +
	    /*AADD._df.format(*/_aOffset1 + ", " + /*AADD._df.format(*/_aMult1 + ", " +
		/*AADD._df.format(*/_aOffset2 + ", " + /*AADD._df.format(*/_aMult2 + "> ";
    }

    public Object clone() { 
	return new SAINodeIndex(_nGid, _nID1, _nID2, 
				_aOffset1, _aMult1, _aOffset2, _aMult2);
    }
    
    public void toNext(){
    	offset = 1;
    }
    public void toPrev(){
    	offset = -1;
    }
    public void clear(){
    	offset = 0;
    }
}
