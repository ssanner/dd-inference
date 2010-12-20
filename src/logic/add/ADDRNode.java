// Note this class hierarchy is really a mess... need to clean up
// some day.  This is just a generic int reference node for an ADD.

package logic.add;

import java.util.*;

public class ADDRNode {
    
    // This is assigned by an outer struct and gives
    // access to formula assoc with global-ID, is
    // analogy of prop var ID for ADDs.
    public int _lid;
    
    public ADDRNode(int lid) {
	_lid = lid;
    }

    public void set(int lid) {
	_lid = lid;
    }
    
    public String toString() {
	return "<" + _lid + ">";
    }

    public String toString(Object context, int depth) {
	StringBuffer sb = new StringBuffer();	
	if (context instanceof ADD) {
	    sb.append("[ " + ((ADD)context).getNode(_lid).toString(context,depth+1));
	} else {
	    return "[ ERROR: " + context.getClass() + " ] "; 
	}
	sb.append("]");	
	return sb.toString();
    }
    
    public int hashCode() {
	return _lid;
    }
    
    public boolean equals(Object o) {
	return (_lid == ((ADDRNode)o)._lid);
    }
}

