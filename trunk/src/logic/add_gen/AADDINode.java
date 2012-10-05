package logic.add_gen;

import graph.Graph;

import java.text.DecimalFormat;
import java.util.*;

public class AADDINode extends ADDNode {
    
    // This is assigned by an outer struct and gives
    // access to formula assoc with global-ID, is
    // analogy of prop var ID for ADDs.
    public int _nGlobalID;
    public int   _nLow, _nHigh;
    public Gen _aLowOffset,  _aLowMult;
    public Gen _aHighOffset, _aHighMult;
    //public double _dMinLower, _dMinUpper;
    //public double _dMaxLower, _dMaxUpper;
    
    public AADDINode(int lid, int gid) {
	_nLocalID  = lid;
	_nGlobalID = gid;
	//_dMinLower = _dMinUpper = Double.NaN;
	//_dMaxLower = _dMaxUpper = Double.NaN;
    }
   
    public AADDINode(int lid, int gid, int low, int high, Gen o_l,
			Gen m_l, Gen o_h, Gen m_h) {
		_nLocalID = lid;
		_nGlobalID = gid;
		_nLow = low;
		_nHigh = high;
		_aLowOffset = o_l;
		_aLowMult = m_l;
		_aHighOffset = o_h;
		_aHighMult = m_h;
		// _dMinLower = _dMinUpper = Double.NaN;
		// _dMaxLower = _dMaxUpper = Double.NaN;
	}

	public String toString(Object context, int depth) {
		StringBuffer sb = new StringBuffer();
		sb.append("[ #" + _nLocalID + " v" + _nGlobalID + " ");

		// Internal bounds
		// sb.append("<" + ADD._df.format(_dMinLower) + "..." +
		// ADD._df.format(_dMaxLower) + " ; " +
		// ADD._df.format(_dMinUpper) + "..." +
		// ADD._df.format(_dMaxUpper) + "> ");

		if (context instanceof AADD) {

			// Node level cache
			ADDNode n1 = ((AADD) context).getNode(_nHigh);
			if (n1 != null) {
				sb.append("\n" + indent(depth) + "<"
						+ _aHighOffset + ","
						+ _aHighMult + ">");
				if (_nHigh == _nLow) {
					sb.append("\n" + indent(depth) + "<"
							+ _aLowOffset + ","
							+ _aLowMult + "> LIN:");
					sb.append(" [ " + n1.toString(((AADD) context), depth + 1)
							+ "] ");
				} else {
					sb.append(" h:[ "
							+ n1.toString(((AADD) context), depth + 1) + "] ");
				}
			} else {
				sb.append("h:[null] ");
			}

			if (_nHigh != _nLow) {

				ADDNode n2 = ((AADD) context).getNode(_nLow);
				if (n2 != null) {
					sb.append("\n" + indent(depth) + "<"
							+ _aLowOffset + ","
							+ _aLowMult + ">" + " l:[ "
							+ n2.toString(((AADD) context), depth + 1) + "] ");
				} else {
					sb.append("l:[null] ");
				}
				sb.append("] ");
			}

		}

		return sb.toString();
	}
    

	public String toStringLocal(Object context) {
		StringBuffer sb = new StringBuffer();
		sb.append("[ #" + _nLocalID + " v" + _nGlobalID + " ");

		if (context instanceof AADD) {

			// Node level cache
			ADDNode n1 = ((AADD) context).getNode(_nHigh);
			if (n1 != null) {
				sb.append("\n   <"
						+ _aHighOffset + ","
						+ _aHighMult + ">");
				if (_nHigh == _nLow) {
					sb.append("\n   <"
							+ _aLowOffset + ","
							+ _aLowMult + "> LIN:");
					sb.append(" [ #" + n1._nLocalID + " ] ");
				} else {
					sb.append(" h:[ #" + n1._nLocalID + " ] ");
				}
			} else {
				sb.append("h:[null] ");
			}

			if (_nHigh != _nLow) {

				ADDNode n2 = ((AADD) context).getNode(_nLow);
				if (n2 != null) {
					sb.append("\n   <"
							+ _aLowOffset + ","
							+ _aLowMult + ">" + " l:[ #"
							+ n2._nLocalID + " ] ");
				} else {
					sb.append("l:[null] ");
				}
				sb.append(" ] ");
			}

		}

		return sb.toString();
	}

    public void toGraph(Object context, Graph g) {

		if (context instanceof AADD) {

			// Node level cache
			g.addNodeLabel("#" + _nLocalID, "x" + _nGlobalID /* + " : #" + _nLocalID*/);
			if (DD.USE_COLOR) {
				if (DD.USE_FESTIVE) 
					g.addNodeColor("#" + _nLocalID, "green"); // green, lightblue
				else
					g.addNodeColor("#" + _nLocalID, "lightblue"); // green, lightblue
			}
			g.addNodeShape("#" + _nLocalID, "ellipse");
			g.addNodeStyle("#" + _nLocalID, "filled");

			ADDNode n1 = ((AADD) context).getNode(_nHigh);
			if (n1 != null) {
				g.addUniLink("#" +_nLocalID, "#" + _nHigh, "black", "solid", 
						"<" + _aHighOffset.toString() + " + " + 
						(_aHighMult.toString()) + " * >");
				n1.toGraph(((AADD) context), g);
				g.addUniLink("#" +_nLocalID, "#" + _nLow, "black", "dashed", 
						"<" + (_aLowOffset.toString()) + " + "
						+ (_aLowMult.toString()) + " * >");
				if (_nHigh != _nLow) {
					ADDNode n2 = ((AADD) context).getNode(_nLow);
					if (n2 != null) n2.toGraph(((AADD) context), g);
				}
			} 
		} else {
			System.out.println("[ ERROR GENERATING GRAPH: " + context.getClass() + " ] ");
		}
    }
}

