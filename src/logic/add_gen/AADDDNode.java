package logic.add_gen;

import graph.Graph;

import java.util.*;

public class AADDDNode extends ADDNode {
    
    public Gen _aLower;
    public Gen _aUpper;

    public String _sLowerLabel; // Optional labels, i.e. which max contributed?
    public String _sUpperLabel; 
    
    // For a single value
    public AADDDNode(int lid, Gen val) {
    	_nLocalID  = lid;
    	_aLower    = val;
    	_aUpper    = val;
    	_sLowerLabel = null;
    	_sUpperLabel = null;
    }
    
    // For a range value
    public AADDDNode(int lid, Gen min, Gen max) {
	_nLocalID = lid;
	_aLower   = min;
	_aUpper   = max;
	_sLowerLabel = null;
	_sUpperLabel = null;
    }
    
    // For a range value
    public AADDDNode(int lid, Gen min, Gen max, 
		    String lower_label, String upper_label) {
	_nLocalID = lid;
	_aLower   = min;
	_aUpper   = max;
	_sLowerLabel = lower_label;
	_sUpperLabel = upper_label;
    }
    
    public String toString() {
	return "*" + _aLower + "*";
    }

    public String toString(Object context, int depth) {
	
	if (_aUpper == _aLower) {
	    String label = "";
	    if (_sUpperLabel != null) {
		label = ": <" + _sUpperLabel + "> ";
	    }
	    return "[ #" + _nLocalID + " <" + _aLower + "> ] " + label;
	} else {
	    String label = "";
	    if (_sLowerLabel != null ||_sUpperLabel != null) {
		if (_sLowerLabel == null) {
		    label = ": <" + _sUpperLabel + "> ";
		} else if (_sUpperLabel == null) {
		    label = ": <" + _sLowerLabel + "> ";
		} else if (_sUpperLabel.equals(_sLowerLabel)) {
		    label = ": <" + _sUpperLabel + "> ";
		} else {
		    label = ": <" + _sLowerLabel + "," + _sUpperLabel + "> ";
		}
		label = ": " + _sUpperLabel;
	    }
	    return "[ #" + _nLocalID + " <" + _aLower 
		                      + "," + _aUpper + "> ] " + label;
	}
    }
    
    
    public void toGraph(Object context, Graph g) {
    	g.addNode("#" + _nLocalID);
		g.addNodeLabel("#" + _nLocalID, (_aLower.toString()));
		if (DD.USE_COLOR) {
			if (DD.USE_FESTIVE) 
				g.addNodeColor("#" + _nLocalID, "red"); // red, darkred, lightsalmon
			else
				g.addNodeColor("#" + _nLocalID, "lightsalmon"); // red, darkred, lightsalmon
		}
		g.addNodeShape("#" + _nLocalID, "box");
		g.addNodeStyle("#" + _nLocalID, "filled");

    }

}
