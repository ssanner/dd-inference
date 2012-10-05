package logic.add_gen;

import java.util.*;

public class DSAINodeIndex 
  implements Comparable {

    public int _nGid;
    public int _nID1;
    public int _nID2;
    
    public double _dOffset1;
    public double _dMult1;
    public double _dOffset2;
    public double _dMult2;
    public double _dDistance;

    public static final boolean USE_GRAY_CODE = true;

    // 10 bits = 3 decimal places
    //
    // Need to work this out mathematically based on PRECISION and
    // distance calculation.
    //
    //  0  = 1e-16
    // 12  = 1e-13
    // 24? = 1e-10
    public static final int SHIFT_BITS = 25;

    public DSAINodeIndex(int gid, int low, int high,
			double o_l, double m_l, double o_h, double m_h) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_dOffset1  = o_l;
	_dMult1    = m_l;
	_dOffset2  = o_h;
	_dMult2    = m_h;
	_dDistance = Math.sqrt((o_l*o_l) + (o_h*o_h) + (m_l*m_l) + (m_h*m_h));
    }
    
    public DSAINodeIndex(int gid, int low, int high,
			double o_l, double m_l, double o_h, double m_h,
			double perturb) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_dOffset1  = o_l;
	_dMult1    = m_l;
	_dOffset2 = o_h;
	_dMult2   = m_h;
	_dDistance = Math.sqrt((o_l*o_l) + (o_h*o_h) + (m_l*m_l) + (m_h*m_h)) + perturb;
    }

    public void set(int gid, int low, int high,
		    double o_l, double m_l, double o_h, double m_h) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_dOffset1  = o_l;
	_dMult1    = m_l;
	_dOffset2  = o_h;
	_dMult2    = m_h;
	_dDistance = Math.sqrt((o_l*o_l) + (o_h*o_h) + (m_l*m_l) + (m_h*m_h));
    }
    
    public void set(int gid, int low, int high,
		    double o_l, double m_l, double o_h, double m_h,
		    double perturb) {
	_nGid  = gid;
	_nID1  = low;
	_nID2 = high;
	_dOffset1  = o_l;
	_dMult1    = m_l;
	_dOffset2 = o_h;
	_dMult2   = m_h;
	_dDistance = Math.sqrt((o_l*o_l) + (o_h*o_h) + (m_l*m_l) + (m_h*m_h)) + perturb;
    }
      
    public int hashCode() {
	// Perfect hash up to 2^10 = 1024 nodes for IDs			
	/*
	long d1 = Double.doubleToRawLongBits(Math.abs(_dOffset1)) >>> SHIFT_BITS;
	int  i1 = (int)(d1 + (d1 >> 32));
	long d2 = Double.doubleToRawLongBits(Math.abs(_dOffset2)) >>> SHIFT_BITS;
	int  i2 = (int)(d2 + (d2 >> 32));
	i2 = (i2 << 16) + (i2 >> 16);

	long d3 = Double.doubleToRawLongBits(Math.abs(_dMult1)) >>> SHIFT_BITS;
	int  i3 = (int)(d3 + (d3 >> 32));
	i3 = (i3 << 24) + (i3 >> 8);
	long d4 = Double.doubleToRawLongBits(Math.abs(_dMult2)) >>> SHIFT_BITS;
	int  i4 = (int)(d4 + (d4 >> 32));
	i4 = (i4 << 8) + (i4 >> 24);

	return _nGid + (_nID1 << 10) + (_nID2 << 20) + -i1 + i2 + -i3 + i4;
	*/

	long d1;
	int  i1;
	d1 = (Double.doubleToRawLongBits(Math.abs(_dDistance))+1) >>> SHIFT_BITS;
	i1 = (int)(d1 + (d1 >> 32));

	return _nGid + (_nID1 << 10) + (_nID2 << 20) + -i1;
    }
    
    public boolean equals(Object o) {
	DSAINodeIndex s = (DSAINodeIndex)o;
	return ((_nGid == s._nGid) && 
		(_nID1 == s._nID1) && 
		(_nID2 == s._nID2) &&
		(Math.abs(_dOffset1 - s._dOffset1) <= DAADD.PRECISION) &&
		(Math.abs(_dMult1   - s._dMult1)   <= DAADD.PRECISION) &&
		(Math.abs(_dOffset2 - s._dOffset2) <= DAADD.PRECISION) &&
		(Math.abs(_dMult2   - s._dMult2)   <= DAADD.PRECISION));
    }

    public int compareTo(Object o) {

	DSAINodeIndex s = (DSAINodeIndex)o;

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
	int sign_dist = sign(this._dDistance - s._dDistance); 
	if (sign_dist != 0) {
	    return sign_dist;
	}

	// Now check for equivalence within precision!
	if (DAADD.USE_NODE_MERGING &&
	    Math.abs(_dOffset1 - s._dOffset1) <= DAADD.PRECISION &&
	    Math.abs(_dMult1   - s._dMult1)   <= DAADD.PRECISION &&
	    Math.abs(_dOffset2 - s._dOffset2) <= DAADD.PRECISION &&
	    Math.abs(_dMult2   - s._dMult2)   <= DAADD.PRECISION) {
	    return (0);
	}

	// Now perform standard ordered check
	if (this._dOffset1 < s._dOffset1) {
	    return (-1);
	} else if (this._dOffset1 > s._dOffset1) {
	    return (1);
	}

	if (this._dMult1 < s._dMult1) {
	   return (-1);
	} else if (this._dMult1 > s._dMult1) {
	    return (1);
	}

	if (this._dOffset2 < s._dOffset2) {
	    return (-1);
	} else if (this._dOffset2 > s._dOffset2) {
	    return (1);
	}

	if (this._dMult2 < s._dMult2) {
	    return (-1);
	} else if (this._dMult2 > s._dMult2) {
	    return (1);
	}	

	// If we got here definitely an error
	if (DAADD.USE_NODE_MERGING) {
	    System.out.println("ERROR: SAINodeIndex.compareTo(): Should not get here!");
	    System.out.println(this + "\n" + s);
	    Object o1 = null; o1.toString();
	}
	return (0);
    }

    public String toString() {
	return "\n<" + _nGid + ", " + _nID1 + ", " + _nID2 + ", *" + _dDistance + "*, " +
	    /*AADD._df.format(*/_dOffset1 + ", " + /*AADD._df.format(*/_dMult1 + ", " +
		/*AADD._df.format(*/_dOffset2 + ", " + /*AADD._df.format(*/_dMult2 + "> ";
    }

    public Object clone() { 
	return new DSAINodeIndex(_nGid, _nID1, _nID2, 
				_dOffset1, _dMult1, _dOffset2, _dMult2);
    }

    public static int    sign(double v) { return (v == 0.0d) ? 0 : ((v < 0.0d) ? -1 : 1); }
}
