/****************************************************************************************[Solver.h]
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

#ifndef Glucose_Solver_h
#define Glucose_Solver_h

#include "ClauseManager.h"
#include "Restart.h"
#include "core/SolverTypes.h"
#include "mtl/Alg.h"
#include "mtl/Heap.h"
#include "mtl/Vec.h"
#include "utils/Options.h"
#include "utils/Random.h"
#include "utils/Verbose.h"
#include "pfactory/include/Groups.h"
#include "pfactory/include/Communicators.h"


namespace Glucose {

enum Stats { nbGlues, nbBin, nbUn, lcmTested, lcmReduced, nbWalk, walkTime, nbFlips, noDecisionConflict, nbReducedClauses, nbSelfSubsumptions, nbStats };
enum ParallelStats {
    nbImportedUnits,
    nbExportedUnits,
    nbImportedTwoWatched,
    nbExportedTwoWatched,
    nbImportedOneWatched,
    nbExportedOneWatched,
    nbGoodImported,
    nbRemovedInPurgatory,
    nbParallelStats
};
//=================================================================================================
// Solver -- the main class:

class Restart;
class GlucoseRestart;
class LubyRestart;
class ClauseManager;
class GlucoseClauseManager;
class TargetPhase;
class TrailSaving;


class Solver {
   public:
    // Constructor/Destructor:
    //
    Solver();
    Solver(const Solver& s);
    virtual ~Solver();

    // Problem specification:
    //
    Var newVar(bool polarity = true, bool dvar = true);   // Add a new variable with parameters specifying variable mode.

    bool addClause(const vec<Lit>& ps);    // Add a clause to the solver.
    bool addEmptyClause();                 // Add the empty clause, making the solver contradictory.
    bool addClause(Lit p);                 // Add a unit clause to the solver.
    bool addClause(Lit p, Lit q);          // Add a binary clause to the solver.
    bool addClause(Lit p, Lit q, Lit r);   // Add a ternary clause to the solver.
    bool addClause_(vec<Lit>& ps);         // Add a clause to the solver without making superflous internal copy. Will
                                           // change the passed vector 'ps'.

    // Solving:
    //
    bool          simplify();                              // Removes already satisfied clauses.
    virtual lbool solve();                                 // Search without assumptions.
    bool          solve(const vec<Lit>& assumps);          // Search for a model that respects a given set of assumptions.
    lbool         solveLimited(const vec<Lit>& assumps);   // Search for a model that respects a given set of assumptions (With resource constraints).
    bool          solve(Lit p);                            // Search for a model that respects a single assumption.
    bool          solve(Lit p, Lit q);                     // Search for a model that respects two assumptions.
    bool          solve(Lit p, Lit q, Lit r);              // Search for a model that respects three assumptions.
    bool          okay() const;                            // FALSE means solver is in a conflicting state


    // Variable mode:
    //
    void setPolarity(Var  v,
                     bool b);             // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void setDecisionVar(Var v, bool b);   // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool        value(Var x) const;        // The current value of a variable.
    lbool        value(Lit p) const;        // The current value of a literal.
    lbool        modelValue(Var x) const;   // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool        modelValue(Lit p) const;   // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int          nAssigns() const;          // The current number of assigned literals.
    int          nClauses() const;          // The current number of original clauses.
    int          nClauses(int n) const;     // The number of clauses of a given size
    int          nLearnts() const;          // The current number of learnt clauses.
    int          nVars() const;             // The current number of variables.
    virtual void printStats();
    void         printHeaderCurrentSearchSpace() const;
    void         printCurrentSearchSpace() const;
    virtual void displayModel();

    // Resource contraints:
    //
    void setConfBudget(int64_t x);
    void setPropBudget(int64_t x);
    void budgetOff();
    void interrupt();        // Trigger a (potentially asynchronous) interruption of the solver.
    void clearInterrupt();   // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void         checkGarbage(double gf);
    void         checkGarbage();


    // Parallel managment
    pFactory::Group*                  threadsGroup;
    pFactory::Communicator<int>*      unitLiteralsCommunicator;
    pFactory::Communicator<vec<Lit>*>*oneWatchCommunicator, *twoWatchCommunicator;
    void        setComponents(pFactory::Group* pthreadsGroup, pFactory::Communicator<int>* ulc, pFactory::Communicator<vec<Lit>*>* owc,
                              pFactory::Communicator<vec<Lit>*>* twc);
    bool        importUnaries();
    void        exportUnary(Lit l);
    void        exportTwoWatched(Clause& c);
    void        exportOneWatched(Clause& c);
    void        exportClauseDuringSearch(Clause& c);
    void        exportClauseDuringConflictAnalysis(Clause& c);
    bool        importWatches(pFactory::Communicator<vec<Lit>*>* communicator, bool (Solver::*import)(vec<Lit>&));
    bool        importTwoWatched(vec<Lit>& data);
    bool        importOneWatched(vec<Lit>& data);
    bool        shrinkClauseDuringImport(vec<Lit>& data);   // return true if clause is sat, false otherwise
    bool        importClauses();
    inline bool parallelMode() const { return threadsGroup != nullptr; }
    bool        randomizeFirstDescent;

    // Extra results: (read-only member variable)
    //
    bool       solvedByLS;
    vec<lbool> model;      // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;   // If problem is unsatisfiable (possibly under assumptions),
                           // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    double  realTimeStart;
    bool    parsing;
    bool    showModel;
    Verbose verbose;
    double  var_decay;
    double  clause_decay;
    double  random_var_freq;
    double  random_seed;
    Random  random;
    int     ccmin_mode;     // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int     phase_saving;   // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool    rnd_pol;        // Use random polarities for branching heuristics.
    bool    rnd_init_act;   // Initialize variable activities with a small random value.
    double  garbage_frac;   // The fraction of wasted memory allowed before a garbage collection is triggered.


    // Statistics: (read-only member variable)
    //
    uint64_t           solves, starts, decisions, rnd_decisions, propagations, conflicts;
    vec<unsigned long> stats, parallelStats;
    // Certified UNSAT
    FILE* certifiedOutput;
    bool  certifiedUNSAT;
    bool  vbyte;

    void write_char(unsigned char c) const;
    void write_lit(int n) const;
    template <typename T>
    void addToDrat(T& lits, bool add);

    //
    friend class GlucoseRestart;
    GlucoseRestart* glucoseRestart;
    LubyRestart*    lubyRestart;
    Restart*        restart;

    friend class ClauseManager;
    friend class GlucoseClauseManager;
    friend class TiersClauseManager;
    friend class TiersClauseManagerSAT20;
    ClauseManager* clauseManager;

    friend class TrailSaving;
    TrailSaving* trailSaving;

    friend class CCANR;

    // LCM
    bool simplifyAll();
    void simplifyLearnt(CRef cr);
    int  trailRecord;
    void litsEnqueue(int cutP, Clause& c);
    void cancelUntilTrailRecord();
    void simpleUncheckEnqueue(Lit p, CRef from = CRef_Undef);
    CRef simplePropagate();
    bool simplifySetOfLearnts(vec<CRef>&);

    vec<Lit>  simp_learnt_clause;
    vec<CRef> simp_reason_clause;
    void      simpleAnalyze(CRef confl, vec<Lit>& out_learnt, vec<CRef>& reason_clause, bool True_confl);
    // sort learnt clause literal by litValue

    // in redundant
    bool         removed(CRef cr);
    int          useLCM;
    unsigned int LCMUpdateLBD;

    bool useSelfSubsumption;

    // Stable / Focus Mode
    enum SearchMode { stable, focus, onlyStable, onlyFocus };
    SearchMode searchMode;
    void       changeMode();
    friend class TargetPhase;
    TargetPhase* targetPhase;
    uint64_t     ticks, nextChangingPhase, nbChangingPhase;
    bool         walkMode;
    std::string  phasesUsedDuringSearch;

    bool adaptSolver();
    bool adaptStrategies;

   protected:
    // Helper structures:
    //
    struct VarData {
        CRef reason;
        int  level;
    };

    static inline VarData mkVarData(CRef cr, int l) {
        VarData d = {cr, l};
        return d;
    }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) { }
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted {
        const ClauseAllocator& ca;
        explicit WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) { }
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };


    struct VarOrderLt {
        const vec<double>& activity;
        bool               operator()(Var x, Var y) const { return activity[x] > activity[y]; }
        explicit VarOrderLt(const vec<double>& act) : activity(act) { }
    };

    // Solver state:
    //
    bool        ok;                    // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>   clauses;               // List of problem clauses.
    vec<CRef>   learntsCore;           // List of learnt clauses (core or all learnts if glucoseReducer is used
    vec<CRef>   learntsTiers;          // List of tiers learnt clauses
    vec<CRef>   learntsLocal;          // List of tiers learnt clauses
    vec<CRef>   unaryWatchedClauses;   // List of imported clauses (after the purgatory) // TODO put inside ParallelSolver
    double      cla_inc;               // Amount to bump next clause with.
    vec<double> activity;              // A heuristic measurement of the activity of a variable.
    double      var_inc;               // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
        watches;   // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    OccLists<Lit, vec<Watcher>, WatcherDeleted> watchesBin;       // 'watches[lit]' is a list of constraints watching 'lit' (will go
    OccLists<Lit, vec<Watcher>, WatcherDeleted> unaryWatches;     //  Unary watch scheme (clauses are seen when they become empty
    vec<lbool>                                  assigns;          // The current assignments.
    vec<char>                                   polarity;         // The preferred polarity of each variable.
    vec<char>                                   targetPolarity;   // The preferred polarity of each variable.
    vec<char>                                   decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>                                    trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>                                    trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>                                vardata;          // Stores reason and level for each variable.
    int                                         qhead;   // Head of queue (as index into the trail -- no more explicit propagation queue in Glucose).
    int                                         simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t          simpDB_props;        // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>         assumptions;         // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt> order_heap;          // A priority queue of variables ordered with respect to the variable activity.
    double           progress_estimate;   // Set by 'search()'.
    bool             remove_satisfied;    // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in
    // 'simplify'.
    bool useUnaryWatched;   // Enable unary watched literals

    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
    vec<Lit> lastDecisionLevel;

    ClauseAllocator ca;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    vec<char> seen;
    vec<Lit>  analyze_stack;
    vec<Lit>  analyze_toclear;
    vec<Lit>  add_tmp;

    // Resource contraints:
    //
    int64_t conflict_budget;      // -1 means no budget.
    int64_t propagation_budget;   // -1 means no budget.
    bool    asynch_interrupt;


    // Main internal methods:
    //
    void  insertVarOrder(Var x);   // Insert a variable in the decision order priority queue.
    bool  pickPolarityLit(Var x);
    Lit   pickBranchLit();                                               // Return the next decision variable.
    void  newDecisionLevel();                                            // Begins a new decision level.
    void  uncheckedEnqueue(Lit p, CRef from = CRef_Undef);               // Enqueue a literal. Assumes value of literal is undefined.
    bool  enqueue(Lit p, CRef from = CRef_Undef);                        // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef  propagate();                                                   // Perform unit propagation. Returns possibly conflicting clause.
    CRef  propagateUnaryWatches(Lit p);                                  // Perform propagation on unary watches of p, can find only conflicts
    void  cancelUntil(int level);                                        // Backtrack until a certain level.
    void  analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel);   // (bt = backtrack)
    void  analyzeFinal(Lit       p,
                       vec<Lit>& out_conflict);            // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool  litRedundant(Lit p, uint32_t abstract_levels);   // (helper method for 'analyze()')
    lbool search();                                        // Search for a given number of conflicts.
    lbool solve_();                                        // Main solve method (assumptions given in 'assumptions').
    void  removeSatisfied(vec<CRef>& cs);                  // Shrink 'cs' to contain only non-satisfied clauses.
    void  rebuildOrderHeap();

    bool minimizewbr;
    void minimizationWithBinaryResolution(vec<Lit>& out_learnt);
    // Maintaining Variable/Clause activity:
    //
    void varDecayActivity();                   // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void varBumpActivity(Var v, double inc);   // Increase a variable with the current 'bump' value.
    void varBumpActivity(Var v);               // Increase a variable with the current 'bump' value.
    void claDecayActivity();                   // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void claBumpActivity(Clause& c);           // Increase a clause with the current 'bump' value.
    void bumpReasonLiterals(Lit lit);
    // Operations on clauses:
    //
    void attachClause(CRef cr);                        // Attach a clause to watcher lists.
    void detachClause(CRef cr, bool strict = false);   // Detach a clause to watcher lists.
    void attachClausePurgatory(CRef cr);
    void detachClausePurgatory(CRef cr, bool strict = false);
    void removeClause(CRef cr, bool inPurgatory = false);   // Detach and free a clause.
    bool locked(const Clause& c) const;                     // Returns TRUE if a clause is a reason for some implication in the current state.
    bool satisfied(const Clause& c) const;                  // Returns TRUE if a clause is satisfied in the current state.

    // compute LBD
    vec<unsigned int> usedLevels;   // usedLevels[var] contains the current conflict number... Used to count the number of  LBD
    unsigned int      LBDFLAG;
    template <typename T>
    unsigned int computeLBD(T& lits);


    void relocAll(ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel() const;        // Gives the current decisionlevel.
    uint32_t abstractLevel(Var x) const;   // Used to represent an abstraction of sets of decision levels.
    CRef     reason(Var x) const;
    int      level(Var x) const;
    double   progressEstimate() const;   // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget() const;

    void printLit(Lit l) const;
    void printClause(CRef cr) const;
    void printClause(vec<Lit>& lits) const;
};


//=================================================================================================
// Implementation of inline methods:

/****************************************************************
Certified UNSAT proof in binary format
****************************************************************/


inline void Solver::write_char(unsigned char ch) const {
    if(putc_unlocked((int)ch, certifiedOutput) == EOF) exit(1);
}


inline void Solver::write_lit(int n) const {
    for(; n > 127; n >>= 7) write_char(128 | (n & 127));
    write_char(n);
}


template <typename T>
inline void Solver::addToDrat(T& lits, bool add) {
    if(vbyte) {
        if(add)
            write_char('a');
        else
            write_char('d');
        for(int i = 0; i < lits.size(); i++) write_lit(2 * (var(lits[i]) + 1) + sign(lits[i]));
        write_lit(0);
    } else {
        if(!add) fprintf(certifiedOutput, "d ");

        for(int i = 0; i < lits.size(); i++) fprintf(certifiedOutput, "%i ", (var(lits[i]) + 1) * (-2 * sign(lits[i]) + 1));
        fprintf(certifiedOutput, "0\n");
        fflush(certifiedOutput);
    }
}


inline CRef Solver::reason(Var x) const { return vardata[x].reason; }


inline int Solver::level(Var x) const { return vardata[x].level; }


inline void Solver::insertVarOrder(Var x) {
    if(!order_heap.inHeap(x) && decision[x]) order_heap.insert(x);
}

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }


inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }


inline void Solver::varBumpActivity(Var v, double inc) {
    if((activity[v] += inc) > 1e100) {
        // Rescale:
        for(int i = 0; i < nVars(); i++) activity[i] *= 1e-100;
        var_inc *= 1e-100;
    }

    // Update order_heap with respect to new activity:
    if(order_heap.inHeap(v)) order_heap.decrease(v);
}


inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }


inline void Solver::claBumpActivity(Clause& c) {
    if((c.activity() += cla_inc) > 1e20) {
        // Rescale:
        for(unsigned int i : learntsCore) ca[i].activity() *= 1e-20;
        cla_inc *= 1e-20;
    }
}

inline void Solver::checkGarbage() { return checkGarbage(garbage_frac); }


inline void Solver::checkGarbage(double gf) {
    if(ca.wasted() > ca.size() * gf) garbageCollect();
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool Solver::enqueue(Lit p, CRef from) { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }


inline bool Solver::addClause(const vec<Lit>& ps) {
    ps.copyTo(add_tmp);
    return addClause_(add_tmp);
}


inline bool Solver::addEmptyClause() {
    add_tmp.clear();
    return addClause_(add_tmp);
}


inline bool Solver::addClause(Lit p) {
    add_tmp.clear();
    add_tmp.push(p);
    return addClause_(add_tmp);
}


inline bool Solver::addClause(Lit p, Lit q) {
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    return addClause_(add_tmp);
}


inline bool Solver::addClause(Lit p, Lit q, Lit r) {
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    add_tmp.push(r);
    return addClause_(add_tmp);
}


inline bool Solver::locked(const Clause& c) const {
    if(c.size() > 2) return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c;
    return (value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c) ||
           (value(c[1]) == l_True && reason(var(c[1])) != CRef_Undef && ca.lea(reason(var(c[1]))) == &c);
}


inline void Solver::newDecisionLevel() { trail_lim.push(trail.size()); }


inline int Solver::decisionLevel() const { return trail_lim.size(); }


inline uint32_t Solver::abstractLevel(Var x) const { return 1 << (level(x) & 31); }


inline lbool Solver::value(Var x) const { return assigns[x]; }


inline lbool Solver::value(Lit p) const { return assigns[var(p)] ^ sign(p); }


inline lbool Solver::modelValue(Var x) const { return model[x]; }


inline lbool Solver::modelValue(Lit p) const { return model[var(p)] ^ sign(p); }


inline int Solver::nAssigns() const { return trail.size(); }


inline int Solver::nClauses() const { return clauses.size(); }


inline int Solver::nClauses(int sz) const {
    int nb = 0;
    for(int i = 0; i < clauses.size(); i++)
        if(ca[clauses[i]].size() == sz) nb++;
    return nb;
}


inline int Solver::nLearnts() const { return learntsCore.size() + learntsTiers.size() + learntsLocal.size(); }


inline int Solver::nVars() const { return vardata.size(); }


inline void Solver::setPolarity(Var v, bool b) { polarity[v] = b; }


inline void Solver::setDecisionVar(Var v, bool b) {
    decision[v] = b;
    insertVarOrder(v);
}


inline void Solver::setConfBudget(int64_t x) { conflict_budget = conflicts + x; }


inline void Solver::setPropBudget(int64_t x) { propagation_budget = propagations + x; }


inline void Solver::interrupt() { asynch_interrupt = true; }


inline void Solver::clearInterrupt() { asynch_interrupt = false; }


inline void Solver::budgetOff() { conflict_budget = propagation_budget = -1; }


inline bool Solver::withinBudget() const {
    return !asynch_interrupt && (conflict_budget < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget);
}


inline bool Solver::solve(Lit p) {
    budgetOff();
    assumptions.clear();
    assumptions.push(p);
    return solve_() == l_True;
}


inline bool Solver::solve(Lit p, Lit q) {
    budgetOff();
    assumptions.clear();
    assumptions.push(p);
    assumptions.push(q);
    return solve_() == l_True;
}


inline bool Solver::solve(Lit p, Lit q, Lit r) {
    budgetOff();
    assumptions.clear();
    assumptions.push(p);
    assumptions.push(q);
    assumptions.push(r);
    return solve_() == l_True;
}


inline bool Solver::solve(const vec<Lit>& assumps) {
    budgetOff();
    assumps.copyTo(assumptions);
    return solve_() == l_True;
}


inline lbool Solver::solveLimited(const vec<Lit>& assumps) {
    assumps.copyTo(assumptions);
    return solve_();
}


inline bool Solver::okay() const { return ok; }



inline void Solver::printLit(Lit l) const {
    if(value(l) == l_False)
        printf("\033[0;31m");
    if(value(l) == l_True)
        printf("\033[0;34m");
    if(sign(l) == true)
        printf("-");
    printf("%d", var(l) + 1);
    if(value(l) != l_Undef)
        printf("(%d)", level(var(l)));
    printf("\033[0m");
    printf(" ");
}

inline void Solver::printClause(CRef cr) const {
    const Clause &c =ca[cr];
    for(int i = 0; i < c.size(); i++) printLit(c[i]);
    printf("\n");
}


inline void Solver::printClause(vec<Lit>& lits) const {
    for(Lit l : lits) printLit(l);
    printf("\n");
}

//=================================================================================================
// Debug etc:


//=================================================================================================
}   // namespace Glucose

#endif
