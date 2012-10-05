package logic.add_gen;

import graph.Graph;

import java.text.DecimalFormat;
import java.util.*;

public class DAADDINode extends ADDNode {
    
    // This is assigned by an outer struct and gives
    // access to formula assoc with global-ID, is
    // analogy of prop var ID for ADDs.
    public int _nGlobalID;
    public int   _nLow, _nHigh;
    public double _dLowOffset,  _dLowMult;
    public double _dHighOffset, _dHighMult;
    //public double _dMinLower, _dMinUpper;
    //public double _dMaxLower, _dMaxUpper;
    
    public static DecimalFormat _df = new DecimalFormat("#.######");
    
    public DAADDINode(int lid, int gid) {
	_nLocalID  = lid;
	_nGlobalID = gid;
	//_dMinLower = _dMinUpper = Double.NaN;
	//_dMaxLower = _dMaxUpper = Double.NaN;
    }
    
    public DAADDINode(int lid, int gid, int low, int high, double o_l,
			double m_l, double o_h, double m_h) {
		_nLocalID = lid;
		_nGlobalID = gid;
		_nLow = low;
		_nHigh = high;
		_dLowOffset = o_l;
		_dLowMult = m_l;
		_dHighOffset = o_h;
		_dHighMult = m_h;
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

		if (context instanceof DAADD) {

			// Node level cache
			ADDNode n1 = ((DAADD) context).getNode(_nHigh);
			if (n1 != null) {
				sb.append("\n" + indent(depth) + "<"
						+ DAADD._df.format(_dHighOffset) + ","
						+ DAADD._df.format(_dHighMult) + ">");
				if (_nHigh == _nLow) {
					sb.append("\n" + indent(depth) + "<"
							+ DAADD._df.format(_dLowOffset) + ","
							+ DAADD._df.format(_dLowMult) + "> LIN:");
					sb.append(" [ " + n1.toString(((DAADD) context), depth + 1)
							+ "] ");
				} else {
					sb.append(" h:[ "
							+ n1.toString(((DAADD) context), depth + 1) + "] ");
				}
			} else {
				sb.append("h:[null] ");
			}

			if (_nHigh != _nLow) {

				ADDNode n2 = ((DAADD) context).getNode(_nLow);
				if (n2 != null) {
					sb.append("\n" + indent(depth) + "<"
							+ DAADD._df.format(_dLowOffset) + ","
							+ DAADD._df.format(_dLowMult) + ">" + " l:[ "
							+ n2.toString(((DAADD) context), depth + 1) + "] ");
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

		if (context instanceof DAADD) {

			// Node level cache
			ADDNode n1 = ((DAADD) context).getNode(_nHigh);
			if (n1 != null) {
				sb.append("\n   <"
						+ DAADD._df.format(_dHighOffset) + ","
						+ DAADD._df.format(_dHighMult) + ">");
				if (_nHigh == _nLow) {
					sb.append("\n   <"
							+ DAADD._df.format(_dLowOffset) + ","
							+ DAADD._df.format(_dLowMult) + "> LIN:");
					sb.append(" [ #" + n1._nLocalID + " ] ");
				} else {
					sb.append(" h:[ #" + n1._nLocalID + " ] ");
				}
			} else {
				sb.append("h:[null] ");
			}

			if (_nHigh != _nLow) {

				ADDNode n2 = ((DAADD) context).getNode(_nLow);
				if (n2 != null) {
					sb.append("\n   <"
							+ DAADD._df.format(_dLowOffset) + ","
							+ DAADD._df.format(_dLowMult) + ">" + " l:[ #"
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

		if (context instanceof DAADD) {

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

			ADDNode n1 = ((DAADD) context).getNode(_nHigh);
			if (n1 != null) {
				g.addUniLink("#" +_nLocalID, "#" + _nHigh, "black", "solid", 
						"<" + _df.format(_dHighOffset) + " + " + 
						_df.format(_dHighMult) + " * >");
				n1.toGraph(((DAADD) context), g);
				g.addUniLink("#" +_nLocalID, "#" + _nLow, "black", "dashed", 
						"<" + _df.format(_dLowOffset) + " + "
						+ _df.format(_dLowMult) + " * >");
				if (_nHigh != _nLow) {
					ADDNode n2 = ((DAADD) context).getNode(_nLow);
					if (n2 != null) n2.toGraph(((DAADD) context), g);
				}
			} 
		} else {
			System.out.println("[ ERROR GENERATING GRAPH: " + context.getClass() + " ] ");
		}
    }
}

