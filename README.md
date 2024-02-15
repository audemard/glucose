# Glucose SAT solver


This is the release 4.2.1 of the glucose SAT solver. 
It is based on [Minisat 2.2](http://minisat.se/MiniSat.html)

## Presentation 
Glucose is an award winning SAT solver based on a scoring scheme we introduced in 2009 for the clause learning mechanism of so called “Modern” SAT solvers (see our IJCAI’09 paper). It is designed to be parallel, since 2014 and was enterly rebooted in 2021. 
Glucose is developed by a very friendly team: Gilles Audemard and Laurent Simon. 

The name of the Solver name is a contraction of the concept of “glue clauses”, a particular kind of clauses that glucose detects and preserves during search.

Glucose is heavily based on Minisat, so please do cite Minisat also if you want to cite Glucose. Glucose  is based on the [Minisat 2.2](http://minisat.se/MiniSat.html) version. We strongly encourage you to visit the Minisat web pages, and to try the original Minisat too.

## A (very) short analysis of Glucose performances
Learning (in CDCL algorithms) was firstly introduced for completeness. But, if we study all Glucose 2’s traces of the competition 2011, for instance, phase 2, in the categories Applications and Crafted, Glucose 2 learnt 973,468,489 clauses (sum over all traces) but removed 909,123,525 of them, i.e. more than 93% of the clauses are removed. This view is really new and contradicts previous beliefs. Thus, we thought that one of the performance keys of our solver is not only based on the identification of good clauses, but also on the removing of bad ones. As a side effect, by aggressively deleting those clauses, Glucose increases the CDCL incompleteness (keeping learnt clauses is essential for completeness). We should also emphasize here that Glucose 2 was ranked fourth on the parallel track in the SAT 2011 competition beside the fact that it was sequential. This shows that even with a single core, our solver performed better, in user time (not CPU) than many parallel solvers exploiting the 8 cores of the parallel machine. One of the reasons for this is that Glucose 2 is good at finding the shortest (but easiest) proof as possible.

Among the short list of [programs](http://www-cs-faculty.stanford.edu/~knuth/programs.html) of Prof. Don Knuth, you may want to take a deep look at the [SAT13.w](http://www-cs-faculty.stanford.edu/~knuth/programs/sat13.w), his CDCL implementation. Very interesting and insightful. With glucose-techniques inside!

## Features
 
 - Sequential and Parallel solvers
 - Incremental mode
 - Certified UNSAT proofs
 - Good performances on industrial (non crypto) problems.

**Note**: Don’t change the preprocessing switches on this version (you can turn off the preprocessing but when using it, don’t play with the preprocessing options). We were reported some discrepancies in the results when using the -rcheck argument.
You can choose to compile the following Glucose alternatives:

    Glucose sequential (with/without Satelite, decided by command line arguments)
    Glucose sequential, incremental mode
    Glucose sequential, certified unsat proof logging
    Glucose parallel with satelite ( not yet a parallel certified unsat / parallel incremental)

Choose your directory (simp or parallel) and type ‘make’.

## How to use it

We are often asked how to use/install/call our SAT solver.
 
 - Don't forget to install the libz library. It is needed to read .cnf.gz files (compressed cnf). This is probably the most frequent compilation error.
 - You should type "make" into the simp (if you want to preprocess the file) or into the core directory.
 - You may have a few warning (depending on your gcc version) but this should not hurt
 - If Glucose compiles, you need now a CNF file to give it. CNF files are in Dimacs format, i.e. variables are numbers only and the formula is in conjunctive normal form. You may need to spend some time to search the web for this format. It is simple but you may need to write a few lines to handle it/play with it inside your own tool
 - If everything's ok, and if Glucose found an answer to your problem, send us an email (we like to hear successes stories about glucose ) and now you have either
   - To trust Glucose if it says "UNSAT" (your formula has no solution)
   - To run Glucose again with certified UNSAT activated (to check that glucose was correctly answer UNSAT)
   - To read the solution, if Glucose says "SAT". Your solution (with -model activated is printed at the end).


## Papers 

 - "_Predicting Learnt Clauses Quality in Modern SAT Solver_". Gilles Audemard, Laurent Simon, in Twenty-first International Joint Conference on Artificial Intelligence (IJCAI'09), july 2009.
 - "_Glucose: a solver that predicts learnt clauses quality_". Gilles Audemard, Laurent Simon, SAT Competition, 2009.
 - "_Refining restarts strategies for SAT and UNSAT formulae_". Gilles Audemard and Laurent Simon, in Proceedings of the 22nd International Conference on Principles and Practice of Constraint Programming (CP-12), 2012.
 - "_GLUCOSE 2.1: Aggressive – but Reactive – Clause Database Management, Dynamic Restarts_". In Pragmatics of SAT (Workshop of SAT'12), Gilles Audemard and Laurent Simon, Juin 2012.
 - "_Improving Glucose for Incremental SAT Solving with Assumption: Application to MUS Extraction_". Gilles Audemard, Jean-Marie Lagniez, Laurent Simon, in Proceedings of SAT 2013, 2013.
 - "_Lazy Clause Exchange Policy for parallel SAT solvers_". Gilles Audemard, Laurent Simon, in 17th International Conference on Theory and Applications of Satisfiability Testing (SAT'14), 2014.
 - "_Glucose in the SAT 2014 Competition_". Gilles Audemard, Laurent Simon, SAT Competition, 2014.
 - "_Glucose and Syrup in the SAT Race 2015_". Gilles Audemard, Laurent Simon, SAT race 2015.
 - "_Extreme cases in SAT problems_". Gilles Audemard, Laurent Simonn in International Conference on Theory and Applications of Satisfiability Testing (SAT'16), 2016.
 - "_Glucose and Syrup in the SAT’17_". Gilles Audemard, Laurent Simon, SAT competition  2017.
 - "_Glucose and syrup: Nine years in the sat competitions_". illes Audemard, Laurent Simon, SAT competition  2018.
 - "_On the glucose SAT solver_". Gilles Audemard, Laurent Simon, International Journal on Artificial Intelligence Tools 27 (01), 2018.
