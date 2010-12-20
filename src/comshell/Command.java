//////////////////////////////////////////////////////////////////////
//
// File:     Command.java
// Project:  MIE457F Information Retrieval System
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     12/1/2000
//
//////////////////////////////////////////////////////////////////////

// Package definition
package comshell;

// Packages to import
import java.util.*;
import java.io.*;
import java.lang.*;

/**
 * Supports methods for a command line interface
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class Command
{
    /** Static members **/
    public final static int MAX_INPUT    = 8192; // Script length limit
    public final static int MAX_COMMANDS = 100;

    /** Basic common commands **/
    public final static int LISTE   = 0;
    public final static int SET     = 1;
    public final static int HELP    = 2;
    public final static int ECHO    = 3;
    public final static int EXEC    = 4;
    public final static int REXEC   = 5;
    public int UNKNOWN = 6; /* This changes as new commands are added */

    /** Command/Help index **/
    public String[] comnames   = new String[MAX_COMMANDS];
    public String[] helpstring = new String[MAX_COMMANDS];

    /** Class members **/
    public int type; 
    public boolean echo;
    public ArrayList params;
    public BufferedReader br;
    public InputStream is;  // Input Stream to read from
    public PrintStream os;  // Output Stream to write to

    /** Constructor
     *  @param is InputStream to process
     *  @param os OutputStream to write data to
     **/
    public Command(InputStream is, PrintStream os)
    {
	// Initialize streams
	this.is = is;
	this.os = os;

	// Initialize common commands
	comnames[LISTE]   = "listenv"; helpstring[LISTE] = null;
	comnames[SET]     = "setenv";  helpstring[SET]   = null;
	comnames[HELP]    = "help";    helpstring[HELP]  = null;
	comnames[ECHO]    = "echo";    helpstring[ECHO]  = null;
	comnames[EXEC]    = "exec";    helpstring[EXEC]  = null;
	comnames[REXEC]   = "return";  helpstring[REXEC] = null;

	br = null;
	echo = false;
	type = UNKNOWN;
	params = new ArrayList();
    }

    /** Registers a new command with the interface
     *  @param cname   The command name (as it will be invoked)
     *  @param helpstr Help information to printed out when listing
     *                 this command
     *  @return ID for the new command
     **/
    public int addCommand(String cname, String helpstr)
    {
	comnames[UNKNOWN]   = cname;
	helpstring[UNKNOWN] = helpstr;
	type++; // This is the initial value of type which should equal UNKNOWN
	return UNKNOWN++;
    }

    /** Turns echo on or off
     *  @param e Set true for echo on
     **/
    public void setEcho(boolean e)
    {
	echo = e;
    }

    /** Clears the last command and resets to UNKNOWN
     **/
    public void clear()
    {
	type = UNKNOWN;
	params.clear();
    }

    /** Returns number of params for command
     *  @return Number of valid parameters
     **/
    public int numParams()
    {
	return params.size();
    }

    /** Retrieves a parameter for a command
     *  @param index Which parameter to access
     *  @return The string for the parameter index
     **/
    public String getParam(int index)
    {
	if (index >= params.size()) return null;
        return (String)params.get(index);        
    }

    /** Parses the current input stream.  Handles file/terminal IO
     ** as well as Windows and UNIX carriage-return/linefeed issues.
     **/
    // A basic helper function to receive a string from the input
    public void parseStream() throws IOException
    {
	String s, comline;
	StringTokenizer st;
	byte[] b = new byte[MAX_INPUT];
	int l, i;

	/* Clear old command info */
	clear();

	/* If BufferedReader non-empty from previous read, use that,
	 * otherwise attempt to read a new string from the input stream -
	 * this allows reading from both STDIN and redirected files which
	 * are read all at one time */
	if ((br == null) || ((comline = br.readLine()) == null))
	    {
		l = is.read(b);
		if (l<0) { /* If script, should have ended with quit */
		    System.out.println("Stream empty!"); 
		    return;
		}
		s = new String(b); 
		br = new BufferedReader(new StringReader(s.substring(0,l-1)));
		//os.println("\n\nRd>>> " + s.substring(0,l-1));
		comline = br.readLine();
	    }
	
	/* Now we have a valid command line in comline */
	if (echo) os.println(" [" + comline + "]");
	if (comline == null) return;
	st = new StringTokenizer(comline, "\"\t \r\n", true); // true: return delim

	if (st.countTokens() < 1) return;

	// Determine command type
	s = st.nextToken();
	for (i=0, type = UNKNOWN; i<UNKNOWN; i++)
	    if (s.equalsIgnoreCase(comnames[i]))
		{
		    type = i;
		    break;
		}

	// Parse parameters into string array - this is nasty code, read
	// at your own risk... surprisingly it does work though. :)
	boolean append = false, past_first_append = false;
	while (st.hasMoreTokens())
	{
	  s = st.nextToken();
	  if ((s.equals(" ") || s.equals("\t") || s.equals("\r") || s.equals("\n")))
	    continue;
	  //System.out.println("\nToken: " + s);
	  if (s.equals("\""))
	    {
	      append = !append; // Toggle
	      if (append == false) 
		past_first_append = false;
	      continue;
	    }
	  if (past_first_append)
	    params.set(params.size() - 1, params.get(params.size() - 1) + " " + s);
	  else
	    params.add(s);
	  past_first_append = append;
	}
    }
}


