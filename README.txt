dd-inference -- Implementation of Decision Diagrams for 
                Probabilistic Inference.

Copyright (C) 2004-2010, Scott Sanner (ssanner [@] gmail.com)

License: MPL 1.1

         **Except all other 3rd-party software (mostly .jar's 
           included for convenience) and data content (mostly
           Bayes Net Repository .bif files), which retain 
           their original copyright and license.
           

Basic RDDLSim Installation and Invocation
=========================================

dd-inference/ provides the following subdirectories:

    src   All source code (.java files)
    bin   All binaries (.class files)
    lib   All 3rd party libraries (.jar files)
    files All supplementary files (.rddl files, etc.)

Always ensure that all .jar files in lib/ are included in your
CLASSPATH for both Java compilation and at Java runtime.  We highly
recommend that you use Eclipse for Java development:

    http://www.eclipse.org/downloads/

In Eclipse the CLASSPATH libraries can be set via 

    Project -> Properties -> Java Build Path -> Libraries Tab

For running RDDLSim from a terminal, we provide two scripts

    run     For Windows/Cygwin and UNIX/Linux systems
    run.bat For the Windows CMD prompt

In both cases, run these scripts from the **rddlsim/**
directory with the class name as an argument, e.g.

    Windows/Cygwin and UNIX/Linux: ./run rddl.sim.Simulator
    Windows CMD prompt:            .\run.bat rddl.sim.Simulator

You can pass up to 10 arguments to these scripts as required.


Instructions for using Decision Diagrams and Prob. Inference
============================================================

See README.BAYES_NET and README.MDP in directory 'src/prob'.


GraphViz RDDL Visualization
===========================

Although not required to run the basic RDDL simulator facilities, some
additional GraphViz visualization tools are provided.  

To enable Java Graphviz visualization:

- Download and install GraphViz on your system:
 
  http://www.graphviz.org/

- Make sure "dot" and "neato" (including ".exe" if running on Windows)
  are in your PATH, i.e., you can execute them from any home directory

Run graph.Graph.main() and verify that a cleanly formatted Java window
displaying a graph appears.

Run rddl.viz.RDDL2Graph.main() to convert RDDL files to interactively
view DBNs for RDDL instances in a Java viewer and export GraphViz 
graph specifications for publication. 