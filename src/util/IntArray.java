/**
 * IntArray.java
 *
 *
 * Created: Mon Jul 8 13:07:49 2002
 *
 * @author Scott Sanner
 * @version 1.0
 * 
 * Note that because of _ref, this IntArray is really specific to
 * this implementation!
 */
package util;

import java.util.Arrays;
import java.util.Iterator;
import java.util.Random;
import java.util.TreeSet;

// TODO: Verify remove()!!!

/**
 * An efficient class for maintaining integer sets.
 */
public class IntArray implements Comparable {

	public int[] l; // array

	public int count = 0; // num elements
	
	public IntArray() {
		l = new int[4];
		count = 0;
	}
	
	//
	// Note: This constructor does *not* perform a copy or a sort!
	public IntArray(int[] val) {
		l = val;
		count = val.length;
	}

	// This constructor performs a copy
	public IntArray(int[] val, int size) {
		l = new int[size];
		count = size; // Start set with 0 elements and add
		System.arraycopy(val, 0, l, 0, size);
	}

	public int hashCode() {
		int val = 0;
		for (int i = 0; i < count; i++) {
			val = (val << 1) + l[i];
		}
		return val; // i.e. equal		
	}
	
	public void add(int oid) {
		
		if (count >= l.length) {
			// Enlarge the array.
			int[] temp = new int[l.length << 1];
			System.arraycopy(l, 0, temp, 0, count);
			l = temp;
		} 
		l[count++] = oid;
	}
	
	public void addAll(IntArray a) {
		
		if ((count + a.count - 1) >= l.length) {
			// Enlarge the array.
			int[] temp = new int[Math.max(count + a.count, l.length << 1)];
			System.arraycopy(l, 0, temp, 0, count);
			l = temp;
		} 
		for (int i = 0; i < a.count; i++)
			l[count++] = a.l[i];
	}

	public int find(int oid) {
		for (int i = 0; i < count; i++)
			if (l[i] == oid) return i;
		return -1;
	}
	
	public void set(int index, int oid) {

		if (index >= l.length) {
			// Enlarge the array.
			int[] temp = new int[index + 4];
			System.arraycopy(l, 0, temp, 0, count);
			l = temp;
		} 
		
		if (index >= count) {
			count = index + 1;
		}
		l[index] = oid;
	}
	
	public boolean equals(Object o) {
		IntArray s = (IntArray)o;
		if (count != s.count) {
			return false; // if count < s.count => false
		} else {
			int val = 0;
			for (int i = 0; val == 0 && i < count; i++) {
				val = l[i] - s.l[i];
			}
			return (val == 0); // i.e. equal
		}		
	}
	
	public int compareTo(Object o) {
		IntArray s = (IntArray)o;
		if (count != s.count) {
			return s.count - count; // if s.count > count => positive (longer 1st)
		} else {
			int val = 0;
			for (int i = 0; val == 0 && i < count; i++) {
				val = l[i] - s.l[i];
			}
			return val;
		}
	}
	
	public void copy(IntArray is) {
		count = is.count;
		if (l.length < count) {
			l = new int[count];
		}
		System.arraycopy(is.l, 0, l, 0, count);
	}
	
	public int[] toArray() {
		int[] ret = new int[count];
		System.arraycopy(l, 0, ret, 0, count);
		return ret;
	}
	
	public void removeIndex(int index) {

		//
		// Remove the value if we found it.
		if (index >= 0) {

			//
			// Copy the array over by one to remove the old ID.
			System.arraycopy(l, index + 1, l, index, count - index - 1);
			count--;
		}
	}
	
	public String toString() {
		StringBuffer sb = new StringBuffer("[ ");
		for (int i = 0; i < count; i++) {
			sb.append(l[i] + " ");
		}
		sb.append("]");
		return sb.toString();
	}

	public void clear() {
		count = 0;
	}

	public Object clone() {
		IntArray n = new IntArray();
		n.count = count;
		n.l = new int[l.length];
		System.arraycopy(l, 0, n.l, 0, count);
		return n;
	}

	public boolean isEmpty() {
		return (count == 0);
	}
	
	public static void main(String[] args) {
		Test1();
		
		for (int sz = 10; sz <= 1000000; sz += sz) {
			Test2(sz);
		}
	}
	
	public static void Test1() {
		TreeSet ts = new TreeSet();
		
		IntArray ts1 = new IntArray(); 
		ts1.add(1);
		ts1.add(2);
		ts1.add(1);
		ts1.add(2);
		
		IntArray ts2 = new IntArray();
		ts2.add(2);
		ts2.add(3);
		ts2.add(2);
		ts2.add(3);
		
		IntArray ts3 = new IntArray();
		ts3.add(3);
		ts3.add(4);
		ts3.add(4);
		ts3.add(3);
		
		IntArray ts4 = new IntArray();
		ts4.add(3);
		ts4.add(1);
		ts4.add(2);
		
		IntArray ts5 = new IntArray();
		ts5.add(2);
		ts5.add(4);
		ts5.add(3);
		
		IntArray ts6 = new IntArray();
		ts6.add(5);
		ts6.add(6);

		IntArray ts7 = new IntArray();
		ts7.add(1);
		ts7.add(2);
		ts7.add(3);
		ts7.add(4);
		
		ts.add(ts1); 
		ts.add(ts2); 
		ts.add(ts3); 
		ts.add(ts4); 
		ts.add(ts5); 
		ts.add(ts6);
		ts.add(ts7);
		
		System.out.println(ts);

	}
	
	public static void Test2(int max) {
		Random rg = new Random();
		
		TreeSet ts = new TreeSet();
		IntArray yes = null;
		IntArray no = new IntArray(); no.add(-1); no.add(-2);
		for (int i = 0; i < max; i++) {
			int sz = rg.nextInt(3) + 2;
			IntArray s = new IntArray();
			for (int j = 0; j < sz; j++) {
				s.add(rg.nextInt(100));
			}
			ts.add(s);
			if (i == (int)(max/2)) yes = s; 
		}
		
		long ctime = System.currentTimeMillis();
		for (int t = 0; t < 10000; t++) { ts.contains(yes); ts.contains(no); }
		System.out.print(max + ": true/" + ts.contains(yes) + 
				           " false/" + ts.contains(no));
		long etime = System.currentTimeMillis() - ctime;
		System.out.println(", time = " + etime + " ms");
	}
}
