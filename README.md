# Glucose SAT solver

This is the release 4.1 of the glucose SAT solver. 
It is based on [Minisat 2.2](http://minisat.se/MiniSat.html)

**Glucose is now parallel**
 
You can call it Glucose Parallel or Glucose-Syrup (a lot of glucose in it).
An original mechanism for clause sharing (as described in the SAT 2014 paper, based on a 1-Watched literal scheme).
Can work with a lot of cores and limited memory. There is no determinism in the parallel version.

Very good performances on industrial (non crypto) problems.

**Note**: Don’t change the preprocessing switches on this version (you can turn off the preprocessing but when using it, don’t play with the preprocessing options). We were reported some discrepancies in the results when using the -rcheck argument.
You can choose to compile the following Glucose alternatives:

    Glucose sequential (with/without Satelite, decided by command line arguments)
    Glucose sequential, incremental mode
    Glucose sequential, certified unsat proof logging
    Glucose parallel with satelite ( not yet a parallel certified unsat / parallel incremental)

Choose your directory (simp or parallel) and type ‘make’.

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
