/***************************************************************************************[Main.cc]
 Glucose -- Copyright (c) 2009-2014, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                LRI  - Univ. Paris Sud, France (2009-2013)
                                Labri - Univ. Bordeaux, France

 Syrup (Glucose Parallel) -- Copyright (c) 2013-2014, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                Labri - Univ. Bordeaux, France

Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose (sources until 2013, Glucose 3.0, single core) are exactly the same as Minisat on which it
is based on. (see below).

Glucose-Syrup sources are based on another copyright. Permissions and copyrights for the parallel
version of Glucose-Syrup (the "Software") are granted, free of charge, to deal with the Software
without restriction, including the rights to use, copy, modify, merge, publish, distribute,
sublicence, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

- The above and below copyrights notices and this permission notice shall be included in all
copies or substantial portions of the Software;
- The parallel version of Glucose (all files modified since Glucose 3.0 releases, 2013) cannot
be used in any competitive event (sat competitions/evaluations) without the express permission of
the authors (Gilles Audemard / Laurent Simon). This is also the case for any competitive event
using Glucose Parallel as an embedded SAT engine (single core or not).


--------------- Original Minisat Copyrights

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include <core/CCANR.h>
#include <errno.h>
#include <parallel/ParallelSolver.h>
#include <signal.h>
#include <sys/resource.h>
#include <zlib.h>

#include "core/Dimacs.h"
#include "core/TrailSaving.h"
#include "simp/SimpSolver.h"
#include "utils/Options.h"
#include "utils/ParseUtils.h"
#include "utils/System.h"

using namespace Glucose;


// Values for reproducibility
#ifndef GIT_HASH
#define GIT_HASH "(not defined)"
#endif
#ifndef COMPILE_TIME
#define COMPILE_TIME "(not defined)"
#endif
#ifndef GIT_BRANCH
#define GIT_BRANCH "(not defined)"
#endif

//=================================================================================================

static const char *_certified = "CORE -- CERTIFIED UNSAT";

IntOption  verb("MAIN", "verb", "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
BoolOption mod("MAIN", "model", "show model.", false);
BoolOption pre("MAIN", "pre", "Completely turn on/off any preprocessing.", true);
IntOption  cpu_lim("MAIN", "cpu-lim", "Limit on CPU time allowed in secondS->\n", INT32_MAX, IntRange(0, INT32_MAX));
IntOption  mem_lim("MAIN", "mem-lim", "Limit on memory usage in megabyteS->\n", INT32_MAX, IntRange(0, INT32_MAX));
//       BoolOption opt_incremental ("MAIN","incremental", "Use incremental SAT solving",false);

BoolOption   opt_certified(_certified, "certified", "Certified UNSAT using DRUP format", false);
StringOption opt_certified_file(_certified, "certified-output", "Certified UNSAT output file", "NULL");
BoolOption   opt_vbyte(_certified, "vbyte", "Emit proof in variable-byte encoding", false);

static const char *_parallel = "PARALLEL";
static IntOption   ncores(_parallel, "ncores", "number of cores", 1, IntRange(0, 100));


static Solver *solver;


// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) {
    printf("\n");
    printf("c *** INTERRUPTED ***\n");
    solver->interrupt();
}


void limitRessourcesUsage() {
    // Set limit on CPU-time:
    if(cpu_lim != INT32_MAX) {
        rlimit rl;
        getrlimit(RLIMIT_CPU, &rl);

        if(rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max) {
            rl.rlim_cur = cpu_lim;
            if(setrlimit(RLIMIT_CPU, &rl) == -1)
                printf("c WARNING! Could not set resource limit: CPU-time.\n");
            else
                printf("c Limit cpu time to %d\n", cpu_lim.operator int());
        }
    }

    // Set limit on virtual memory:
    if(mem_lim != INT32_MAX) {
        rlim_t new_mem_lim = (rlim_t)mem_lim * 1024 * 1024;
        rlimit rl;
        getrlimit(RLIMIT_AS, &rl);
        if(rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max) {
            rl.rlim_cur = new_mem_lim;
            if(setrlimit(RLIMIT_AS, &rl) == -1) printf("c WARNING! Could not set resource limit: Virtual memory.\n");
        }
    }

    // Change to signal-handlers that will only notify the solver and allow it to terminate
    // voluntarily:
    signal(SIGINT, SIGINT_interrupt);
    signal(SIGXCPU, SIGINT_interrupt);
    signal(SIGTERM, SIGINT_interrupt);
    signal(SIGABRT, SIGINT_interrupt);
}


//=================================================================================================
// Main:

int main(int argc, char **argv) {
    try {
        printf("c\nc This is glucose reboot --  based on MiniSAT (Many thanks to MiniSAT team)\nc\n");
        printf("c reproducibility: git-hash %s\nc reproducibility: git-branch %s\nc reproducibility: compilation-time %s\nc\n", GIT_HASH, GIT_BRANCH,
               COMPILE_TIME);


        setUsageHelp("c USAGE: %s [options] <input-file>\n\n  where input may be either in plain or gzipped DIMACS->\n");


#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw);
        newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
        _FPU_SETCW(newcw);
        // printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //

        parseOptions(argc, argv, true);

        SimpSolver *S            = new SimpSolver();
        double      initial_time = cpuTime();

        S->parsing            = 1;
        S->use_simplification = pre;
        S->verbose.verbosity  = verb;
        S->showModel          = mod;
        S->realTimeStart      = realTime();
        S->certifiedUNSAT     = opt_certified;
        S->vbyte              = opt_vbyte;
        if(S->certifiedUNSAT) {
            if(!strcmp(opt_certified_file, "NULL")) {
                S->vbyte           = false;   // Cannot write binary to stdout
                S->certifiedOutput = fopen("/dev/stdout", "wb");

                S->verbose.log(NORMAL, "c\nc Write unsat proof on stdout using text format\nc\n");
            } else
                S->certifiedOutput = fopen(opt_certified_file, "wb");
            const char *name = opt_certified_file;
            S->verbose.log(NORMAL, "c\nc Write unsat proof on %s using %s format\nc\n", name, S->vbyte ? "binary" : "text");
        }


        limitRessourcesUsage();


        if(argc == 1) printf("c Reading from standard input... Use '--help' for help.\n");

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if(in == NULL) printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

        if(S->useLCM) printf("c enable lazy clause minimisation\n");
        if(S->clauseManager->clauseManagerType == ClauseManagerType::glucose)
            printf("c original glucose learnt clause manager\n");
        else
            printf("c 3-tiers learnt clause manager\n");
        if(S->trailSaving->active) printf("c enable trail saving\n");
        switch(S->searchMode) {
            case Glucose::SimpSolver::SearchMode::stable:
            case Glucose::SimpSolver::SearchMode::focus:
                printf("c Target phase\n");
                break;
            case Glucose::SimpSolver::SearchMode::onlyStable:
                printf("c stable phase\n");
                break;
            case Glucose::SimpSolver::SearchMode::onlyFocus:
                printf("c focus phase\n");
                break;
        }

        S->verbose.log(NORMAL, "c ========================================[ Problem Statistics ]===========================================\n");
        S->verbose.log(NORMAL, "c |                                                                 \n");

        parse_DIMACS(in, *S);
        gzclose(in);

        S->verbose.log(NORMAL, "c |  Number of variables:  %12d\n", S->nVars());
        S->verbose.log(NORMAL, "c |  Number of clauses:    %12d\n", S->nClauses());

        double parsed_time = cpuTime();
        S->verbose.log(NORMAL, "c |  Parse time:           %12.2f s\n", parsed_time - initial_time);
        S->verbose.log(NORMAL, "c | \n");


        S->parsing = 0;
        if(pre /* && !S->isIncremental()*/) {
            printf("c | Preprocessing will be fully done\n");
            S->eliminate(true);
            double simplified_time = cpuTime();
            S->verbose.log(NORMAL, "c |  Simplification time:  %12.2f s \n", simplified_time - parsed_time);
        }
        int nb2 = S->nClauses(2), nb3 = S->nClauses(3), nb = S->nClauses();

        S->verbose.log(NORMAL, "c |  Number of clauses:    %12d - binaries: %d (%d %%) - ternaries: %d (%d %%)\n", S->nClauses(),nb2, (nb2*100)/nb, nb3, (nb3*100)/nb);
        printf("c | \n");

        S->verbose.log(NORMAL, "c =========================================================================================================\n");

        if(!S->okay()) {
            if(S->certifiedUNSAT) fprintf(S->certifiedOutput, "0\n"), fclose(S->certifiedOutput);
            S->verbose.log(NORMAL, "Solved by simplification\n");
            S->printStats();
            S->verbose.log(NORMAL, "\n");
            S->verbose.log(NORMAL, "s UNSATISFIABLE\n");
            exit(20);
        }

        ParallelSolver *parallelSolver;
        if(ncores == 1)
            solver = S;
        else {
            parallelSolver = new ParallelSolver();
            parallelSolver->createSolvers(S, ncores);
            solver = parallelSolver;
        }

        lbool ret = solver->solve();

        solver->printStats();
        printf("\n");

        printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s INDETERMINATE\n");

        if(S->showModel && ret == l_True) solver->displayModel();


#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);   // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch(OutOfMemoryException &) {
        solver->verbose.log(NORMAL, "c =========================================================================================================\n");
        printf("s INDETERMINATE\n");
        exit(0);
    }
}
