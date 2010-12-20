//////////////////////////////////////////////////////////////////////
//
// File:     CommandInterface.java
// Project:  MIE457F Information Retrieval System
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     12/1/2000
//
//////////////////////////////////////////////////////////////////////

// Package definition
package comshell;

// Packages to import
import java.io.*;
import java.util.*;

/**
 * Handles universal commands and basic maintenance for the command
 * shell
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class CommandInterface
{
    /** Static constant members **/
    public final static int MAX_INPUT = 4096;
    
    /** Local data members **/
    public InputStream is;       // Input Stream to read from
    public PrintStream os;       // Output Stream to write to
    public HashMap bindings;     // Env. variable bindings
    public Command command;      // The parsed command struct
    public LinkedList is_stack;  // Stack of streams
    public boolean _bProcessing; // True of actively processing

    /** Constructor
     *  @param is InputStream for shell input
     *  @param os OutputStream for shell output
     **/
    public CommandInterface(InputStream is, PrintStream os)
    {
	this.is = is;
	this.os = os;
	command = new Command(is, os);
        bindings = new HashMap();
	is_stack = new LinkedList();
    }
    
    /** Are we at the top level of the execution stack?  (When exec is
     *  called, the newly exec'ed input stream is pushed onto the
     *  execution stack.  This allows one script to call another and
     *  retain its current position.)
     *  @return True if top level stream
     **/
    public boolean isStreamStackEmpty()
    {
	return (is_stack.size() == 0);
    }

    /** Pushes a new command stream onto the execution stack
     *  @param is Command stream to push
     **/
    public void pushStream(InputStream is)
    {
	is_stack.addFirst(is);
    }

    /** Pops the current command stream from the execution stack
     *  @return The command stream that is popped
     **/
    public InputStream popStream()
    {
	return (InputStream)is_stack.removeFirst();
    }

    /** Registers a new environmental variable binding (local to this
	shell only)
     *  @param varname Environmental variable name
     *  @param value   Environmental variable binding
     **/
    public void setBindings(String varname, String value)
    {
	bindings.put(varname.toUpperCase(), value);
    }

    /** Gets an environmental variable binding (local to this shell
     *  only)
     *  @param varname The binding to retrieve
     *  @return The binding (if null returns the empty string)
     **/
    public String getBindings(String varname)
    {
	if (varname == null) 
	    return "[Null Key]";
	else if (!bindings.containsKey(varname.toUpperCase()))
	    return "";
	else
	    return (String)bindings.get(varname.toUpperCase());
    }

    /** Initializes the environmental variable bindings from a file
     *  @param filename File name to load env var bindings from
     **/
    public void initEnvVarsFromFile(String filename)
    {
	if (filename == null) return;
		
	try {
	    String varname, value;
	    InputStream in = new FileInputStream(filename);
	    byte[] b = new byte[MAX_INPUT];
			
	    int l = in.read(b);
	    String s = new String(b);
	    //System.out.println(s);
	    StringTokenizer st = new StringTokenizer(s.substring(0,l-1), "\n\r\t\"");
			
	    while (st.hasMoreTokens())
		{
		    varname = st.nextToken().trim();
		    //System.out.println("varname: " + varname);
		    if (!st.hasMoreTokens()) break;
		    value = st.nextToken().trim();
		    //System.out.println("value: " + value);
		    setBindings(varname, value);
		}
	} catch (IOException e) {}
    }

    /** Handles the 'listenv' command
     **/
    public void listEnv()
    {
	os.println();
	Iterator i = bindings.keySet().iterator();
	String s;
		
	while (i.hasNext())
	    {
		s = (String)i.next();
		os.println(s + ": '" + getBindings(s) + "'");
	    }
    }
    
    /** Handles the 'setenv' command
     **/
    public void setEnv()
    {
	int i, vartype;
	if (command.numParams() != 2)
	    {
		os.println("Illegal number of parameters");
		return;
	    }
		
	bindings.put(command.getParam(0).toUpperCase(), command.getParam(1));
    }
    
    /** Handles the 'exec' command
     *  @param filename File to execute
     **/
    public void exec(String filename)
    {
	try 
	    {
		InputStream e = new FileInputStream(filename);
		pushStream(command.is);
		command.is = e;

	    } catch(IOException e)
		{
		    os.println("\nCould not open filename '" + filename + "'.\n");
		}
    }

    /** Handles the 'return' command (to return execution to the calling
     *  script (if any).
     **/
    public void exec_return()
    {
	try 
	    {
		command.is.close();
		if (!isStreamStackEmpty())
		    {
			command.is = popStream();
		    }
		else
		    {
			os.println("\nTop level stream returned, continuing...\n");
		    }

	    } catch(IOException e)
		{
		    os.println("\nError closing current input stream.\n");
		}		
    }

    /** Handles the 'help' command - prints the command menu
     **/
    public void printHelp()
    {
	int i;

	os.println("\nlistenv                             - list env vars and bindings");
	os.println("setenv <var> <val>                  - set env variables");
	os.println("echo {on|off}                       - turns com line echoing on/off");
	os.println("exec <filename>                     - execute a script");
	os.println("return                              - returns from script");
	os.println("help                                - this menu");

	// Print user added command help
	for (i=0; i<command.UNKNOWN; i++)
	    if (command.helpstring[i] != null)
		os.println(command.comnames[i] + command.helpstring[i]);

    }
    
    /** Returns true if command being actively processed
     */
    public boolean commandInProgress() {
    	return _bProcessing;
    }
    
    /** Parses a command from the current input stream and determines
     *  if it is locally executable.  If not, it calls the command
     *  handler which should be overridden by any derived class.
     **/
    public void getCommand() throws IOException
    {
	boolean locally_serviceable = true;
	
	while (locally_serviceable)
	    {
		os.print("\n> ");
		_bProcessing = false; // Blocking on input
		command.parseStream();
		_bProcessing = true;
		
		if (command.type == command.UNKNOWN)
		    ; // Do nothing... os.println("\nUnknown command");
		else if (command.type == command.LISTE)
		    listEnv();
		else if (command.type == command.SET)
		    setEnv();
		else if (command.type == command.HELP)
		    printHelp();
		else if (command.type == command.EXEC)
		    {
			if (command.numParams() == 1)
			    exec(command.getParam(0));	
		    }
		else if (command.type == command.REXEC)
		    exec_return();
		else if (command.type == command.ECHO) 
		    {
			if (command.numParams() == 1)
			    {
				if (command.getParam(0).equalsIgnoreCase("Off"))
				    command.setEcho(false);
				else if (command.getParam(0).equalsIgnoreCase("On"))
				    command.setEcho(true);
			    }
		    }
		else
		    locally_serviceable = false;
	    }
		_bProcessing = false;
    }
}
    
    





