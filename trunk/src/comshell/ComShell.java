//////////////////////////////////////////////////////////////////////
//
// File:     ComShell.java
// Project:  MIE457F Information Retrieval System
// Author:   Scott Sanner, University of Toronto (ssanner@cs.toronto.edu)
// Date:     12/1/2000
//
//////////////////////////////////////////////////////////////////////

// Package definition
package comshell;

// Packages to import
import java.io.*;
import java.lang.*;
import java.util.*;

/**
 *   This class represents a simple example of how to use the command
 *   shell package.  Other implementations of a command shell should
 *   build their own local version of this class.  Note that input can
 *   come from a script rather than the command line and as usual,
 *   output can be redirected.
 *
 * @version   1.0
 * @author    Scott Sanner
 * @language  Java (JDK 1.3)
 **/
public class ComShell
{
    /* Encapsulated Objects */
    public CommandInterface pCom;

    /* Class-defined commands */
    public int              COMMANDA;
    public int              COMMANDB;
    public int              QUIT;

    /* Constants */
    public final static int    MAX_INPUT = 4096;
    public final static String PREFS_FILE = "prefs.txt";
   
    /**
     * Main - Initializes the main window
     **/
    public static void main(String args[]) 
    {
	ComShell comshell = new ComShell();
	comshell.run();
    } 
    
    /** 
     * Constructor - Initializes user-defined commands and environmental vars 
     **/
    public ComShell()
    {
	pCom = new CommandInterface(System.in, System.out);
	
	// Initialize a set of commands
	COMMANDA = pCom.command.addCommand("commanda", "            - command a");
	COMMANDB = pCom.command.addCommand("commandb", "            - command b");
	QUIT     = pCom.command.addCommand("quit", "                - quit application");

	// Initialize environmental variable bindings from preferences file
	pCom.initEnvVarsFromFile(PREFS_FILE);
    }
    
    /***********************************************************
     * Main command line handler
     *
     * Note: To add a command, add a command name and help string
     *       using CommandInterface.addCommand() and then 
     *       implement the handler code below.  (See Constructor)
     ***********************************************************/
    public void run()
    {
	while (pCom.command.type != QUIT)
	{
	    try {
		pCom.getCommand();
	    } catch (IOException e) {
		System.out.println("IO Error");
		continue;
	    }
	    
	    /***********************************************************
	     * Command: A
	     ***********************************************************/
	    if (pCom.command.type == COMMANDA)
		{
		    int i, n = pCom.command.numParams();
		    System.out.println("\nCommand A: " + n + " parameters");
		    
		    for (i=0; i<n; i++)
			System.out.println("  Param "+(i+1)+": " +pCom.command.getParam(i));

		}
	    
	    /***********************************************************
	     * Command: B
	     ***********************************************************/
	    if (pCom.command.type == COMMANDB)
		{
		    System.out.println("\nCommand B, binding for env. var 'port': " + pCom.getBindings("PORT"));
		}

	    /***********************************************************
	     * Command: Quit
	     ***********************************************************/
	    else if (pCom.command.type == QUIT)
		{
		    System.out.println("\nExiting application...");		
		}
		
	}
    }
}




