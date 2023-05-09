/***************************************************************************************[Solver.cc]
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

#include "core/Solver.h"

#include <cmath>
#include <iomanip>
#include <iostream>

#include "TargetPhase.h"
#include "TrailSaving.h"
#include "core/CCANR.h"
#include "mtl/Sort.h"
#include "mtl/Vec.h"
#include "pfactory/include/Communicators.h"
#include "pfactory/include/Groups.h"
#include "utils/System.h"


using namespace Glucose;

//=================================================================================================
// Options:


static const char *_cat = "CORE";

static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false));
static DoubleOption opt_random_var_freq(_cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable", 0,
                                        DoubleRange(0, true, 1, true));
static DoubleOption opt_random_seed(_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption    opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption    opt_phase_saving(_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption   opt_rnd_init_act(_cat, "rnd-init", "Randomize the initial activity", false);
static DoubleOption opt_garbage_frac(_cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20,
                                     DoubleRange(0, false, HUGE_VAL, false));
static IntOption    opt_restart_mode(_cat, "restart", "Restart mode (0=glucose, 1=luby)", 0);
static IntOption    opt_reduce_mode(_cat, "reduce", "Reduce mode (0=glucose, 1=core/tiers/local)", 1);
static IntOption    opt_search_mode(_cat, "search", "Search mode (0=target, 1=focus, 2=stable)", 0);
static BoolOption   opt_walk_mode(_cat, "walk", "Use random walk (ccanr)", true);

static BoolOption opt_lcm(_cat, "lcm", "Use inprocessing vivif (ijcai17 paper)", true);
static BoolOption opt_save_trail(_cat, "savetrail", "Save Trail (sat20 paper)", false);

static BoolOption opt_self_sub(_cat, "self-sub", "Use Self Subsumption (ictai09 paper)", false);


//=================================================================================================
// Search and solve
//=================================================================================================

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts.
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search() {
    assert(ok);
    int      backtrack_level;
    vec<Lit> learnt_clause;
    starts++;
    unsigned int lbd;
    bool         aDecisionWasMade = false;

    if(useLCM && clauseManager->performLCM() && simplifyAll() == false) return l_False;

    for(;;) {
        if(parallelMode() && threadsGroup->isStopped()) return l_Undef;
        if(parallelMode() && decisionLevel() == 0 && importClauses() == false) return l_False;


        CRef confl = propagate();
        if(confl != CRef_Undef) {   // CONFLICT
            conflicts++;
            if(decisionLevel() == 0) return l_False;

            if(!aDecisionWasMade) stats[noDecisionConflict]++;
            aDecisionWasMade = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            lbd = computeLBD(learnt_clause);

            // UPDATEVARACTIVITY trick (see competition'09 companion paper)
            if((searchMode == SearchMode::focus || searchMode == SearchMode::onlyFocus) && lastDecisionLevel.size() > 0) {
                for(Lit l : lastDecisionLevel)
                    if(ca[reason(var(l))].lbd() < lbd) varBumpActivity(var(l));
            }


            glucoseRestart->update(trail.size(), lbd);
            restart->blockRestart();

            if(searchMode == stable || searchMode == onlyStable) targetPhase->updateBestPhase();

            cancelUntil(backtrack_level);

            if(learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);
                stats[Stats::nbUn]++;
                if(parallelMode()) exportUnary(learnt_clause[0]);
            } else {
                CRef cr = ca.alloc(learnt_clause, true);
                ca[cr].lbd(lbd);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                clauseManager->add(cr);
                if(lbd == 2) stats[Stats::nbGlues]++;
                if(learnt_clause.size() == 2) stats[Stats::nbBin]++;
                uncheckedEnqueue(learnt_clause[0], cr);
                if(parallelMode()) exportClauseDuringSearch(ca[cr]);
            }

            if(certifiedUNSAT) addToDrat(learnt_clause, true);

            varDecayActivity();
            claDecayActivity();

            if(conflicts % 10000 == 0 && verbose.verbosity == NORMAL) printCurrentSearchSpace();

            if(adaptStrategies && conflicts == 100000 && adaptSolver()) {
                cancelUntil(0);
                return l_Undef;
            }

        } else {                                                 // NO CONFLICT
            if(restart->triggerRestart() || !withinBudget()) {   // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef;
            }

            if((searchMode == stable || searchMode == onlyStable) && targetPhase->rephasing()) {
                lbool tmp = targetPhase->rephase();
                if(tmp != l_Undef) {
                    verbose.log(NORMAL, "c solved by local search engine\n");
                    return tmp;
                }
            }

            if(decisionLevel() == 0 && !simplify())   // Simplify the set of problem clauses:
                return l_False;

            if(clauseManager->triggerReduce()) clauseManager->reduce();

            Lit next = lit_Undef;
            while(decisionLevel() < assumptions.size()) {   // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if(value(p) == l_True) {   // Dummy decision level:
                    newDecisionLevel();
                } else if(value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    return l_False;
                } else {
                    next = p;
                    break;
                }
            }

            if(next == lit_Undef) {   // New variable decision:
                decisions++;
                next = pickBranchLit();

                if(next == lit_Undef)   // Model found:
                    return l_True;
            }

            if((searchMode == focus || searchMode == stable) && ticks > nextChangingPhase) {
                nextChangingPhase = ticks + nbChangingPhase * 15000000;
                nbChangingPhase++;
                changeMode();
            }

            // Increase decision level and enqueue 'next'
            aDecisionWasMade = true;
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_() {
    model.clear();
    conflict.clear();
    if(!ok) return l_False;

    solves++;
    if(targetPhase != nullptr) targetPhase->initialize();

    trailSaving->initialize();

    lbool status = l_Undef;

    if(verbose.verbosity == NORMAL) printHeaderCurrentSearchSpace();

    // Search:
    while(status == l_Undef) {
        status = search();
        if(!withinBudget()) break;
        if(parallelMode() && threadsGroup->isStopped()) return l_Undef;
    }

    verbose.log(NORMAL, "c\nc\n");

    if(certifiedUNSAT && status == l_False) {   // Want certified output
        if(vbyte) {
            write_char('a');
            write_lit(0);
        } else
            fprintf(certifiedOutput, "0\n");
        fclose(certifiedOutput);
    }

    if(status == l_True) {
        model.growTo(nVars());
        if(solvedByLS) {
            verbose.log(NORMAL, "c solved by local search engine\n");
            for(int i = 0; i < nVars(); i++)
                if(value(i) != l_Undef && level(i) == 0)
                    model[i] = value(i);
                else
                    model[i] = targetPhase->ccanr.assignedToTrue(i) ? l_True : l_False;
        } else
            for(int i = 0; i < nVars(); i++) model[i] = value(i);

        return l_True;
    } else if(status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
lbool Solver::solve() {
    budgetOff();
    assumptions.clear();
    return solve_();
}

//=================================================================================================
// Change strategies
//=================================================================================================


bool Solver::adaptSolver() {
    adaptStrategies = false;
    printf("c try adapt the solver \n");
    float decpc = (float)decisions / (float)conflicts;

    if(decpc <= 1.2) {
        printf("c Adjusting for low decision levels.\n");
        restart                     = glucoseRestart;
        searchMode                  = onlyFocus;
        TiersClauseManager *manager = dynamic_cast<TiersClauseManager *>(clauseManager);
        manager->coreUB             = 5;
        return true;
    }


    if(stats[noDecisionConflict] < 30000) {
        printf("c Adjusting for low successive conflicts.\n");
        restart    = lubyRestart;
        searchMode = onlyFocus;
        var_decay  = 0.999;
        return true;
    }
    return false;
}


void Solver::changeMode() {
    if(searchMode == stable) {
        verbose.log(DEBUGVERBOSE, "Focus\n");
        restart    = glucoseRestart;
        var_decay  = 0.95;
        searchMode = focus;
        phasesUsedDuringSearch += ") - Focus ";
    } else {
        if(searchMode == focus) {
            verbose.log(DEBUGVERBOSE, "Stable\n");
            restart    = lubyRestart;
            var_decay  = 0.75;
            searchMode = stable;
            targetPhase->reset();
            phasesUsedDuringSearch += " - Stable(";
        }
    }
}

//=================================================================================================
// Heuristic, enqueue, propagation and backtrack
//=================================================================================================

Lit Solver::pickBranchLit() {
    Var next = var_Undef;

    // Random decision:
    if(((randomizeFirstDescent && conflicts == 0) || random.nextDouble() < random_var_freq) && !order_heap.empty()) {
        next = order_heap[random.nextInt(order_heap.size())];
        if(value(next) == l_Undef && decision[next]) rnd_decisions++;
    }

    // Activity based decision:
    while(next == var_Undef || value(next) != l_Undef || !decision[next])
        if(order_heap.empty()) {
            next = var_Undef;
            break;
        } else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, pickPolarityLit(next));
}


bool Solver::pickPolarityLit(Var x) {
    if(rnd_pol) return random.nextDouble() < 0.5;
    if(searchMode == focus || targetPolarity[x] == -10) return polarity[x];
    return targetPolarity[x];
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate() {
    CRef confl     = CRef_Undef;
    int  num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    if(useUnaryWatched) unaryWatches.cleanAll();
    while(qhead < trail.size()) {
        Lit           p  = trail[qhead++];   // 'p' is enqueued fact to propagate.
        vec<Watcher> &ws = watches[p];
        Watcher      *i, *j, *end;
        num_props++;

        confl = trailSaving->useSaveTrail(p);
        if(confl != CRef_Undef) return confl;


        // First, Propagate binary clauses
        vec<Watcher> &wbin = watchesBin[p];
        for(auto &binWatch : wbin) {
            Lit imp = binWatch.blocker;

            if(value(imp) == l_False) return binWatch.cref;

            if(value(imp) == l_Undef) uncheckedEnqueue(imp, binWatch.cref);
        }

        // Now propagate other 2-watched clauses
        for(i = j = (Watcher *)ws, end = i + ws.size(); i != end;) {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if(value(blocker) == l_True) {
                *j++ = *i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef    cr        = i->cref;
            Clause &c         = ca[cr];
            Lit     false_lit = ~p;
            if(c[0] == false_lit) c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if(first != blocker && value(first) == l_True) {
                *j++ = w;
                continue;
            }

            // Look for new watch:
            for(int k = 2; k < c.size(); k++)
                if(value(c[k]) != l_False) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }
            ++ticks;

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if(value(first) == l_False) {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while(i < end) *j++ = *i++;
            } else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);

        // unaryWatches "propagation"
        if(useUnaryWatched && confl == CRef_Undef) confl = propagateUnaryWatches(p);
    }


    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


CRef Solver::propagateUnaryWatches(Lit p) {
    CRef          confl = CRef_Undef;
    Watcher      *i, *j, *end;
    vec<Watcher> &ws = unaryWatches[p];
    for(i = j = (Watcher *)ws, end = i + ws.size(); i != end;) {
        // Try to avoid inspecting the clause:
        Lit blocker = i->blocker;
        if(value(blocker) == l_True) {
            *j++ = *i++;
            continue;
        }

        // Make sure the false literal is data[1]:
        CRef    cr = i->cref;
        Clause &c  = ca[cr];
        assert(c.oneWatched());
        Lit false_lit = ~p;
        assert(c[0] == false_lit);   // this is unary watch... No other choice if "propagated"
        i++;
        Watcher w = Watcher(cr, c[0]);
        for(int k = 1; k < c.size(); k++) {
            if(value(c[k]) != l_False) {
                c[0] = c[k];
                c[k] = false_lit;
                unaryWatches[~c[0]].push(w);
                goto NextClauseUnary;
            }
        }

        // Did not find watch -- clause is empty under assignment:
        *j++ = w;

        confl = cr;
        qhead = trail.size();
        // Copy the remaining watches:
        while(i < end) *j++ = *i++;

        // We can add it now to the set of clauses when backtracking
        // printf("*");
        if(true) {
            parallelStats[nbGoodImported]++;
            // Let's find the two biggest decision levels in the clause s.t. it will correctly be propagated when we'll backtrack
            int maxlevel = -1;
            int index    = -1;
            for(int k = 1; k < c.size(); k++) {
                assert(value(c[k]) == l_False);
                assert(level(var(c[k])) <= level(var(c[0])));
                if(level(var(c[k])) > maxlevel) {
                    index    = k;
                    maxlevel = level(var(c[k]));
                }
            }
            detachClausePurgatory(cr, true);   // TODO: check that the cleanAll is ok (use ",true" otherwise)
            assert(index != -1);
            Lit tmp = c[1];
            c[1] = c[index], c[index] = tmp;
            attachClause(cr);
            ca[cr].oneWatched(false);
            ca[cr].exported(2);
        }
    NextClauseUnary:;
    }
    ws.shrink(i - j);

    return confl;
}


void Solver::uncheckedEnqueue(Lit p, CRef from) {
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    trailSaving->reset();
    if(decisionLevel() > level) {
        bool savetrail = trailSaving->onBacktrack(level);

        for(int c = trail.size() - 1; c >= trail_lim[level]; c--) {
            if(savetrail) trailSaving->onCancel(c, level);
            Var x      = var(trail[c]);
            assigns[x] = l_Undef;
            if(phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last())) polarity[x] = sign(trail[c]);
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.
|
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit> &out_learnt, int &out_btlevel) {
    int      pathC = 0;
    Lit      p     = lit_Undef;
    // Generate conflict clause:
    //
    out_learnt.push();   // (leave room for the asserting literal)
    int index = trail.size() - 1;
    lastDecisionLevel.clear();
    int  nbSeenLastDL = 0, nbSeenbeforeLastDL = 0, nbLastDL = 0;
    bool performSelfSubsumption = false;
    do {
        assert(confl != CRef_Undef);   // (otherwise should be UIP)
        Clause &c = ca[confl];


        if(p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }

        if(c.learnt()) {
            clauseManager->updateClause(confl);
            if(parallelMode()) exportClauseDuringConflictAnalysis(c);
        }


        if(useSelfSubsumption) {
            nbLastDL = nbSeenLastDL = nbSeenbeforeLastDL = 0;
            for(int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
                Lit q = c[j];
                if(level(var(q)) >= decisionLevel()) nbLastDL++;
                if(seen[var(q)] && level(var(q)) >= decisionLevel()) nbSeenLastDL++;
                if(seen[var(q)] && level(var(q)) < decisionLevel() && level(var(q)) > 0) nbSeenbeforeLastDL++;
            }
            performSelfSubsumption = nbSeenLastDL >= pathC && pathC > 0 && nbSeenbeforeLastDL >= out_learnt.size() - 1;
        }


        for(int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
            Lit q = c[j];

            if(!seen[var(q)] && level(var(q)) > 0) {
                varBumpActivity(var(q));
                if(searchMode == SearchMode::stable || searchMode == SearchMode::onlyStable) bumpReasonLiterals(q);

                seen[var(q)] = 1;

                if(level(var(q)) >= decisionLevel()) {
                    pathC++;
                    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
                    if(reason(var(q)) != CRef_Undef && ca[reason(var(q))].learnt()) lastDecisionLevel.push(q);
                } else
                    out_learnt.push(q);
            }
        }

        if(useSelfSubsumption && performSelfSubsumption && nbLastDL > 1) {
            stats[nbSelfSubsumptions]++;
            int pos = 0;
            for(int j = 2; j < c.size(); j++)
                if(level(var(c[j])) >= decisionLevel()) {
                    pos = j;
                    break;
                }
            detachClause(confl, true);
            c[0]   = c[pos];
            c[pos] = c[c.size() - 1];
            c.pop();
            if(certifiedUNSAT) addToDrat(c, true);
            attachClause(confl);
        }

        // Select next clause to look at:
        while(!seen[var(trail[index--])])
            ;

        p            = trail[index + 1];
        confl        = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while(pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if(ccmin_mode == 2) {
        uint32_t abstract_level = 0;
        for(i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i]));   // (maintain an abstraction of levels involved in conflict)

        for(i = j = 1; i < out_learnt.size(); i++)
            if(reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level)) out_learnt[j++] = out_learnt[i];

    } else if(ccmin_mode == 1) {
        for(i = j = 1; i < out_learnt.size(); i++) {
            Var x = var(out_learnt[i]);

            if(reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else {
                Clause &c = ca[reason(var(out_learnt[i]))];
                // Thanks to Siert Wieringa for this bug fix!
                for(int k = ((c.size() == 2) ? 0 : 1); k < c.size(); k++)
                    if(!seen[var(c[k])] && level(var(c[k])) > 0) {
                        out_learnt[j++] = out_learnt[i];
                        break;
                    }
            }
        }
    } else
        i = j = out_learnt.size();

    out_learnt.shrink(i - j);

    if(minimizewbr && out_learnt.size() < 30) minimizationWithBinaryResolution(out_learnt);

    // Find correct backtrack level:
    //
    if(out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for(int k = 2; k < out_learnt.size(); k++)
            if(level(var(out_learnt[k])) > level(var(out_learnt[max_i]))) max_i = k;
        // Swap-in this literal at index 1:
        Lit l             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = l;
        out_btlevel       = level(var(l));
    }

    for(auto &v : analyze_toclear) seen[var(v)] = 0;   // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels) {
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while(analyze_stack.size() > 0) {
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause &c = ca[reason(var(analyze_stack.last()))];
        analyze_stack.pop();
        if(c.size() == 2 && value(c[0]) == l_False) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }
        for(int i = 1; i < c.size(); i++) {
            Lit p2 = c[i];
            if(!seen[var(p2)] && level(var(p2)) > 0) {
                if(reason(var(p2)) != CRef_Undef && (abstractLevel(var(p2)) & abstract_levels) != 0) {
                    seen[var(p2)] = 1;
                    analyze_stack.push(p2);
                    analyze_toclear.push(p2);
                } else {
                    for(int j = top; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


void Solver::bumpReasonLiterals(Lit lit) {
    const CRef &reason = vardata[var(lit)].reason;
    if(reason == CRef_Undef) return;
    const Clause &c = ca[reason];
    for(auto i = 1; i < c.size(); ++i) {
        varBumpActivity(var(c[i]));
    }
}


/******************************************************************
 * Minimisation with binary reolution
 ******************************************************************/
void Solver::minimizationWithBinaryResolution(vec<Lit> &out_learnt) {
    // Find the LBD measure
    unsigned int lbd = computeLBD(out_learnt);
    Lit          p   = ~out_learnt[0];

    if(lbd <= 6) {
        LBDFLAG++;

        for(int i = 1; i < out_learnt.size(); i++) usedLevels[var(out_learnt[i])] = LBDFLAG;

        vec<Watcher> &wbin = watchesBin[p];
        int           nb   = 0;
        for(int k = 0; k < wbin.size(); k++) {
            Lit imp = wbin[k].blocker;
            if(usedLevels[var(imp)] == LBDFLAG && value(imp) == l_True) {
                nb++;
                usedLevels[var(imp)] = LBDFLAG - 1;
            }
        }
        int l = out_learnt.size() - 1;
        if(nb > 0) {
            stats[nbReducedClauses]++;
            for(int i = 1; i < out_learnt.size() - nb; i++) {
                if(usedLevels[var(out_learnt[i])] != LBDFLAG) {
                    Lit p         = out_learnt[l];
                    out_learnt[l] = out_learnt[i];
                    out_learnt[i] = p;
                    l--;
                    i--;
                }
            }
            out_learnt.shrink(nb);
        }
    }
}


//=================================================================================================
// Reduction of the learnt clause database
//=================================================================================================


void Solver::removeSatisfied(vec<CRef> &cs) {
    int i, j;
    for(i = j = 0; i < cs.size(); i++) {
        Clause &c = ca[cs[i]];
        if(satisfied(c))
            removeClause(cs[i], c.oneWatched());
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify() {
    assert(decisionLevel() == 0);

    trailSaving->reset();

    if(!ok || propagate() != CRef_Undef) return ok = false;

    if(nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;

    // Remove satisfied clauses:
    removeSatisfied(learntsCore);
    removeSatisfied(learntsTiers);
    removeSatisfied(unaryWatchedClauses);
    if(remove_satisfied)   // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    // simpDB_props = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

//=================================================================================================
// Parallel functions
//=================================================================================================

void Solver::setComponents(pFactory::Group *pthreadsGroup, pFactory::Communicator<int> *ulc, pFactory::Communicator<vec<Lit> *> *owc,
                           pFactory::Communicator<vec<Lit> *> *twc) {
    useUnaryWatched          = true;   // multicore -> unaryWatched in action
    threadsGroup             = pthreadsGroup;
    unitLiteralsCommunicator = ulc;
    oneWatchCommunicator     = owc;
    twoWatchCommunicator     = twc;
    parallelStats.growTo(static_cast<int>(ParallelStats::nbParallelStats), 0);
}

bool Solver::importUnaries() {
    int recvDataULs = 0;
    while(unitLiteralsCommunicator->recv(recvDataULs)) {
        if(value(toLit(recvDataULs)) == l_False) return false;
        if(value(var(toLit(recvDataULs))) == l_Undef) {
            uncheckedEnqueue(toLit(recvDataULs));
            parallelStats[nbImportedUnits]++;
        }
    }
    return true;
}

void Solver::exportUnary(Lit l) {
    unitLiteralsCommunicator->send(toInt(l));
    parallelStats[nbExportedUnits]++;
}


void Solver::exportTwoWatched(Clause &c) {
    auto *learnt_clause_copy = new vec<Lit>();
    for(int p = 0; p < c.size(); p++) learnt_clause_copy->push(c[p]);
    twoWatchCommunicator->send(learnt_clause_copy);
    c.exported(2);
    parallelStats[nbExportedTwoWatched]++;
}


void Solver::exportOneWatched(Clause &c) {
    auto *learnt_clause_copy = new vec<Lit>();
    for(int p = 0; p < c.size(); p++) learnt_clause_copy->push(c[p]);
    oneWatchCommunicator->send(learnt_clause_copy);
    c.exported(2);
    parallelStats[nbExportedOneWatched]++;
}

void Solver::exportClauseDuringSearch(Clause &c) {
    if(c.lbd() <= 2) {
        if(c.size() == 2)
            exportTwoWatched(c);
        else
            exportOneWatched(c);
    }
}

void Solver::exportClauseDuringConflictAnalysis(Clause &c) {
    int          goodlimitsize = 15;
    unsigned int goodlimitlbd  = 5;
    if(c.imported() || c.exported() == 2 || conflicts <= 5000) return;
    c.exported(c.exported() + 1);

    if(c.lbd() == 2 || (c.exported() == 2 && (c.size() < goodlimitsize && c.lbd() <= goodlimitlbd))) {
        exportOneWatched(c);
        c.exported(2);   // not sure because one can import a clause with lbd 2 the first time it becomes very good
    }
}


bool Solver::importWatches(pFactory::Communicator<vec<Lit> *> *communicator, bool (Solver::*import)(vec<Lit> &)) {
    std::vector<vec<Lit> *> receivedCopy;
    std::vector<vec<Lit> *> receivedNoCopy;

    communicator->recvAll(receivedCopy, receivedNoCopy);
    while(!receivedCopy.empty()) {
        vec<Lit> newImportedClause;
        receivedCopy.back()->copyTo(newImportedClause);
        shrinkClauseDuringImport(newImportedClause);
        if(newImportedClause.size() == 1) {
            uncheckedEnqueue(newImportedClause[0]);
            receivedCopy.pop_back();
            continue;
        }
        if(newImportedClause.size() == 0) return false;

        (this->*import)(newImportedClause);
        receivedCopy.pop_back();
    }
    while(!receivedNoCopy.empty()) {
        shrinkClauseDuringImport(*receivedNoCopy.back());
        if(receivedNoCopy.back()->size() == 1) {
            uncheckedEnqueue((*receivedNoCopy.back())[0]);
            receivedNoCopy.pop_back();
            continue;
        }
        if(receivedNoCopy.back()->size() == 0) return false;
        (this->*import)(*receivedNoCopy.back());
        receivedNoCopy.pop_back();
    }
    return true;
}


bool Solver::importTwoWatched(vec<Lit> &data) {
    CRef    crRecv = ca.alloc(data, true);
    Clause &c      = ca[crRecv];
    c.lbd(2);   // It is a very good clause
    c.imported(1);
    learntsCore.push(crRecv);
    parallelStats[nbImportedTwoWatched]++;
    attachClause(crRecv);
    return true;
}


bool Solver::importOneWatched(vec<Lit> &data) {
    CRef    crRecv = ca.alloc(data, true);
    Clause &c      = ca[crRecv];
    c.lbd(c.size() - 1);   // It is a very good clause
    c.imported(1);
    unaryWatchedClauses.push(crRecv);
    attachClausePurgatory(crRecv);
    c.oneWatched(true);
    parallelStats[nbImportedOneWatched]++;
    return true;
}


bool Solver::importClauses() {
    if(importUnaries() == false) return false;
    if(importWatches(twoWatchCommunicator, &Solver::importTwoWatched) == false) return false;
    return importWatches(oneWatchCommunicator, &Solver::importOneWatched);
}


bool Solver::shrinkClauseDuringImport(vec<Lit> &data) {
    int i, j;
    for(i = j = 0; i < data.size(); i++)
        if(value(data[i]) == l_True)
            return true;
        else if(value(data[i]) != l_False)
            data[j++] = data[i];
    data.shrink(i - j);
    return false;
}


//=================================================================================================
// Add/remove variables, clauses...
//=================================================================================================


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).

Var Solver::newVar(bool sign, bool dvar) {
    int v = nVars();
    watches.init(mkLit(v, false));
    watches.init(mkLit(v, true));
    watchesBin.init(mkLit(v, false));
    watchesBin.init(mkLit(v, true));
    unaryWatches.init(mkLit(v, false));
    unaryWatches.init(mkLit(v, true));
    seen.push(0);

    assigns.push(l_Undef);
    vardata.push(mkVarData(CRef_Undef, 0));
    // activity .push(0);
    activity.push(rnd_init_act ? random.nextDouble() * 0.00001 : 0);
    polarity.push(sign);
    targetPolarity.push(sign);
    usedLevels.push(0);
    decision.push();
    trail.capacity(v + 1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec<Lit> &ps) {
    assert(decisionLevel() == 0);
    if(!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p = lit_Undef;
    int i, j, flag = 0;

    vec<Lit> oc;

    if(certifiedUNSAT) {
        for(i = j = 0, p = lit_Undef; i < ps.size(); i++) {
            oc.push(ps[i]);
            if(value(ps[i]) == l_True || ps[i] == ~p || value(ps[i]) == l_False) flag = 1;
        }
    }


    for(i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if(value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if(value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if(flag && certifiedUNSAT) {
        addToDrat(ps, true);
        addToDrat(oc, false);
    }


    if(ps.size() == 0)
        return ok = false;
    else if(ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    } else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause &c = ca[cr];
    assert(c.size() > 1);
    if(c.size() == 2) {
        watchesBin[~c[0]].push(Watcher(cr, c[1]));
        watchesBin[~c[1]].push(Watcher(cr, c[0]));
    } else {
        watches[~c[0]].push(Watcher(cr, c[1]));
        watches[~c[1]].push(Watcher(cr, c[0]));
    }
}


void Solver::detachClause(CRef cr, bool strict) {
    const Clause &c = ca[cr];
    if(c.size() == 1) printf("%d\n", c.learnt());
    assert(c.size() > 1);

    if(c.size() == 2) {
        if(strict) {
            remove(watchesBin[~c[0]], Watcher(cr, c[1]));
            remove(watchesBin[~c[1]], Watcher(cr, c[0]));
        } else {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watchesBin.smudge(~c[0]);
            watchesBin.smudge(~c[1]);
        }
    } else {
        if(strict) {
            remove(watches[~c[0]], Watcher(cr, c[1]));
            remove(watches[~c[1]], Watcher(cr, c[0]));
        } else {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge(~c[0]);
            watches.smudge(~c[1]);
        }
    }
}


void Solver::attachClausePurgatory(CRef cr) {
    const Clause &c = ca[cr];

    assert(c.size() > 1);
    unaryWatches[~c[0]].push(Watcher(cr, c[1]));
}


// The purgatory is the 1-Watched scheme for imported clauses

void Solver::detachClausePurgatory(CRef cr, bool strict) {
    const Clause &c = ca[cr];

    assert(c.size() > 1);
    if(strict)
        remove(unaryWatches[~c[0]], Watcher(cr, c[1]));
    else
        unaryWatches.smudge(~c[0]);
}


void Solver::removeClause(CRef cr, bool inPurgatory) {
    Clause &c = ca[cr];

    if(certifiedUNSAT && c.mark() == 0) addToDrat(c, false);


    if(inPurgatory)
        detachClausePurgatory(cr);
    else
        detachClause(cr);
    // Don't leave pointers to free'd memory!
    if(locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}


template unsigned int Solver::computeLBD<Clause>(Clause &lits);
template unsigned int Solver::computeLBD<vec<Lit> >(vec<Lit> &lits);


template <typename T>
unsigned int Solver::computeLBD(T &lits) {
    int nblevels = 0;
    LBDFLAG++;
    for(int i = 0; i < lits.size(); i++) {
        int l = level(var(lits[i]));
        if(usedLevels[l] != LBDFLAG) {
            usedLevels[l] = LBDFLAG;
            nblevels++;
        }
    }
    return nblevels;
}


//=================================================================================================
// Constructor/Destructor:
//=================================================================================================


Solver::Solver()
    :

      // Parameters (user settable):
      //
      threadsGroup(nullptr), randomizeFirstDescent(false), solvedByLS(false), parsing(false), showModel(false), var_decay(opt_var_decay),
      clause_decay(opt_clause_decay), random_var_freq(opt_random_var_freq), random_seed(opt_random_seed), random(opt_random_seed),
      ccmin_mode(opt_ccmin_mode), phase_saving(opt_phase_saving), rnd_pol(false), rnd_init_act(opt_rnd_init_act), garbage_frac(opt_garbage_frac)

      // Statistics: (formerly in 'SolverStats')
      //
      ,
      solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), certifiedOutput(nullptr), certifiedUNSAT(false),
      vbyte(true), glucoseRestart(new GlucoseRestart(*this)), lubyRestart(new LubyRestart(*this)), useLCM(opt_lcm), LCMUpdateLBD(true),
      useSelfSubsumption(opt_self_sub), targetPhase(nullptr), ticks(0), nextChangingPhase(1023), nbChangingPhase(1), walkMode(opt_walk_mode),
      phasesUsedDuringSearch(""), adaptStrategies(false), ok(true), cla_inc(1), var_inc(1), watches(WatcherDeleted(ca)),
      watchesBin(WatcherDeleted(ca)), unaryWatches(WatcherDeleted(ca)), qhead(0), simpDB_assigns(-1), simpDB_props(0),
      order_heap(VarOrderLt(activity)), progress_estimate(0), remove_satisfied(true), useUnaryWatched(false)

      // Resource constraints:
      //
      ,
      conflict_budget(-1), propagation_budget(-1), asynch_interrupt(false), minimizewbr(false), LBDFLAG(0) {
    if(opt_restart_mode == 0)
        restart = glucoseRestart;
    else
        restart = lubyRestart;

    if(opt_search_mode == 1) {
        searchMode             = onlyFocus;
        restart                = glucoseRestart;
        phasesUsedDuringSearch = "Focus";
    } else {
        if(opt_search_mode == 0) {
            searchMode             = focus;
            restart                = glucoseRestart;
            phasesUsedDuringSearch = "Focus";
        } else {
            searchMode             = onlyStable;
            restart                = lubyRestart;
            phasesUsedDuringSearch = "Stable(";
        }
        targetPhase = new TargetPhase(*this);
    }
    if(opt_reduce_mode == 0)
        clauseManager = new GlucoseClauseManager(*this);
    else
        clauseManager = new TiersClauseManager(*this);


    stats.growTo(static_cast<int>(Stats::nbStats), 0);
    trailSaving = new TrailSaving(*this, opt_save_trail);
}


// Copy constructor
Solver::Solver(const Solver &s)
    :

      // Parameters (user settable):
      //
      threadsGroup(nullptr), randomizeFirstDescent(false), solvedByLS(false), parsing(false), showModel(s.showModel), var_decay(opt_var_decay),
      clause_decay(opt_clause_decay), random_var_freq(opt_random_var_freq), random_seed(opt_random_seed), random(opt_random_seed),
      ccmin_mode(opt_ccmin_mode), phase_saving(opt_phase_saving), rnd_pol(false), rnd_init_act(opt_rnd_init_act), garbage_frac(opt_garbage_frac)

      // Statistics: (formerly in 'SolverStats')
      //
      ,
      solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), certifiedOutput(nullptr), certifiedUNSAT(false),
      vbyte(true), glucoseRestart(new GlucoseRestart(*this)), lubyRestart(new LubyRestart(*this)), useLCM(opt_lcm), LCMUpdateLBD(true),
      useSelfSubsumption(opt_self_sub), targetPhase(nullptr), ticks(0), nextChangingPhase(1023), nbChangingPhase(1), walkMode(opt_walk_mode),
      phasesUsedDuringSearch(""), adaptStrategies(false), ok(true), cla_inc(1), var_inc(1), watches(WatcherDeleted(ca)),
      watchesBin(WatcherDeleted(ca)), unaryWatches(WatcherDeleted(ca)), qhead(0), simpDB_assigns(-1), simpDB_props(0),
      order_heap(VarOrderLt(activity)), progress_estimate(0), remove_satisfied(true), useUnaryWatched(false)

      // Resource constraints:
      //
      ,
      conflict_budget(-1), propagation_budget(-1), asynch_interrupt(false), minimizewbr(false), LBDFLAG(0) {
    realTimeStart = s.realTimeStart;

    if(opt_restart_mode == 0)
        restart = glucoseRestart;
    else
        restart = lubyRestart;

    if(opt_search_mode == 1) {
        searchMode             = onlyFocus;
        restart                = glucoseRestart;
        phasesUsedDuringSearch = "Focus";
    } else {
        if(opt_search_mode == 0) {
            searchMode             = focus;
            restart                = glucoseRestart;
            phasesUsedDuringSearch = "Focus";

        } else {
            searchMode             = onlyStable;
            restart                = lubyRestart;
            phasesUsedDuringSearch = "Stable(";
        }
        targetPhase = new TargetPhase(*this);
    }
    if(opt_reduce_mode == 0)
        clauseManager = new GlucoseClauseManager(*this);
    else
        clauseManager = new TiersClauseManager(*this);


    trailSaving = new TrailSaving(*this, opt_save_trail);

    // Copy clauses.
    s.ca.copyTo(ca);
    ca.extra_clause_field = s.ca.extra_clause_field;

    // Copy all search vectors
    s.watches.copyTo(watches);
    s.watchesBin.copyTo(watchesBin);
    s.unaryWatches.copyTo(unaryWatches);
    s.assigns.memCopyTo(assigns);
    s.vardata.memCopyTo(vardata);
    s.activity.memCopyTo(activity);
    s.seen.memCopyTo(seen);
    s.usedLevels.memCopyTo(usedLevels);
    s.polarity.memCopyTo(polarity);
    s.decision.memCopyTo(decision);
    s.trail.memCopyTo(trail);
    s.order_heap.copyTo(order_heap);
    s.clauses.memCopyTo(clauses);
    s.learntsCore.memCopyTo(learntsCore);
    s.learntsLocal.memCopyTo(learntsLocal);
    s.learntsTiers.copyTo(learntsTiers);
    s.unaryWatchedClauses.copyTo(unaryWatchedClauses);
    s.stats.copyTo(stats);
    s.targetPolarity.memCopyTo(targetPolarity);
}


Solver::~Solver() = default;


//=================================================================================================
// Others methods:
//=================================================================================================


bool Solver::satisfied(const Clause &c) const {
    for(int i = 0; i < c.size(); i++)
        if(value(c[i]) == l_True) return true;
    return false;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit> &out_conflict) {
    out_conflict.clear();
    out_conflict.push(p);

    if(decisionLevel() == 0) return;

    seen[var(p)] = 1;

    for(int i = trail.size() - 1; i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if(seen[x]) {
            if(reason(x) == CRef_Undef) {
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            } else {
                Clause &c = ca[reason(x)];
                //                for (int j = 1; j < c.size(); j++) Minisat (glucose 2.0) loop
                // Bug in case of assumptions due to special data structures for Binary.
                // Many thanks to Sam Bayless (sbayless@cs.ubc.ca) for discover this bug.
                for(int j = ((c.size() == 2) ? 0 : 1); j < c.size(); j++)
                    if(level(var(c[j])) > 0) seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::rebuildOrderHeap() {
    vec<Var> vs;
    for(Var v = 0; v < nVars(); v++)
        if(decision[v] && value(v) == l_Undef) vs.push(v);
    order_heap.build(vs);
}


double Solver::progressEstimate() const {
    double progress = 0;
    double F        = 1.0 / nVars();

    for(int i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


void Solver::printStats() {
    double       cpu_time   = cpuTime();
    double       totalTime  = realTime() - realTimeStart;
    double       mem_used   = memUsedPeak();
    unsigned int nbRestarts = glucoseRestart->nbRestarts + lubyRestart->nbRrestarts;
    verbose.log(NORMAL, "c restarts              : %u (in average: %-12" PRIu64 ")\n", nbRestarts, (nbRestarts > 0 ? conflicts / nbRestarts : 0));
    if(glucoseRestart->nbRestarts > 0)
        verbose.log(NORMAL, "c Glucose restarts      : %u (in average %-12" PRIu64 ") - blocked : %u\n", glucoseRestart->nbRestarts,
                    conflicts / glucoseRestart->nbRestarts, glucoseRestart->nbBlocked);
    else
        verbose.log(NORMAL, "c no Glucose restarts\n");
    verbose.log(NORMAL, "c nb ReduceDB           : %u\n", clauseManager->nbReduced);
    verbose.log(NORMAL, "c nb removed            : %u\n", clauseManager->nbRemoved);
    verbose.log(NORMAL, "c nb learnts glue       : %u\n", stats[Stats::nbGlues]);
    verbose.log(NORMAL, "c nb learnts size 2     : %u\n", stats[Stats::nbBin]);
    verbose.log(NORMAL, "c nb learnts size 1     : %u\n", stats[Stats::nbUn]);
    verbose.log(NORMAL, "c conflicts             : %-12" PRIu64 "   (%.0f /sec)\n", conflicts, conflicts / totalTime);
    verbose.log(NORMAL, "c decisions             : %-12" PRIu64 "   (%4.2f %% random) (%.0f /sec)\n", decisions,
                (float)rnd_decisions * 100 / (float)decisions, decisions / cpu_time);
    verbose.log(NORMAL, "c propagations          : %-12" PRIu64 "   (%.0f /sec)\n", propagations, propagations / totalTime);
    verbose.log(NORMAL, "c nb Modes              : %u\n", nbChangingPhase);
    verbose.log(NORMAL, "c sequence              : %s\n", phasesUsedDuringSearch.c_str());
    verbose.log(NORMAL, "c LCM                   : %lu / %lu \n", stats[lcmReduced], stats[lcmTested]);
    verbose.log(NORMAL, "c bin resolution        : %lu  \n", stats[nbReducedClauses]);
    verbose.log(NORMAL, "c self subsumptions     : %lu  \n", stats[nbSelfSubsumptions]);

    if(walkMode) {
        verbose.log(NORMAL, "c nb flips during walks : %-12" PRIu64 " \n", stats[Stats::nbFlips]);
        verbose.log(NORMAL, "c walk time             : %lu s (%lu walks) \n", stats[Stats::walkTime], stats[Stats::nbWalk]);
    }
    if(parallelMode()) {
        verbose.log(NORMAL, "c unary Imported        : %u\n", parallelStats[nbImportedUnits]);
        verbose.log(NORMAL, "c unary Exported        : %u\n", parallelStats[nbExportedUnits]);
        verbose.log(NORMAL, "c 2W    Imported        : %u\n", parallelStats[nbImportedTwoWatched]);
        verbose.log(NORMAL, "c 2W    Exported        : %u\n", parallelStats[nbExportedTwoWatched]);
        verbose.log(NORMAL, "c 1W    Imported        : %u\n", parallelStats[nbImportedOneWatched]);
        verbose.log(NORMAL, "c 1W    Exported        : %u\n", parallelStats[nbExportedOneWatched]);
        verbose.log(NORMAL, "c Good  Imported        : %u\n", parallelStats[nbGoodImported]);
        verbose.log(NORMAL, "c 1W    removed         : %u\n", parallelStats[nbRemovedInPurgatory]);
    }

    if(mem_used != 0) verbose.log(NORMAL, "c Memory used           : %.2f MB\n", mem_used);
    verbose.log(NORMAL, "c CPU time              : %g s\n", cpu_time);
    verbose.log(NORMAL, "c real time             : %g s\n", realTime() - realTimeStart);
}


template <typename T>
void printElement(T t, int w = 15) {
    std::cout << std::right << std::setw(w) << std::setfill(' ') << t;
}


void Solver::printHeaderCurrentSearchSpace() const {
    if(verbose.verbosity < 1) return;
    printf("c ");
    printElement("conflicts");
    printElement("Restarts");
    printElement("Red", 10);
    printElement("Learnts", 30);
    printElement("Removed");
    printElement("Progress");
    std::cout << std::endl;
}


void Solver::printCurrentSearchSpace() const {
    printf("c ");
    printElement(conflicts);
    printElement(glucoseRestart->nbRestarts + lubyRestart->nbRrestarts);
    printElement(clauseManager->nbReduced, 10);
    std::string red =
        "(" + std::to_string(learntsCore.size()) + "/" + std::to_string(learntsTiers.size()) + "/" + std::to_string(learntsLocal.size()) + ")";
    printElement(red, 30);
    printElement(clauseManager->nbRemoved);
    std::cout << std::setprecision(4);
    printElement(progressEstimate() * 100.);
    std::cout << std::endl;
}


void Solver::displayModel() {
    printf("v ");
    for(int i = 0; i < nVars(); i++)
        if(model[i] != l_Undef) printf("%s%s%d", (i == 0) ? "" : " ", (model[i] == l_True) ? "" : "-", i + 1);
    printf(" 0\n");
}

//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator &to) {
    // All watchers:
    //
    watches.cleanAll();
    watchesBin.cleanAll();
    unaryWatches.cleanAll();

    for(int v = 0; v < nVars(); v++)
        for(int s = 0; s < 2; s++) {
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher> &ws = watches[p];
            for(auto &w : ws) ca.reloc(w.cref, to);
            vec<Watcher> &ws2 = watchesBin[p];
            for(auto &j : ws2) ca.reloc(j.cref, to);
            vec<Watcher> &ws3 = unaryWatches[p];
            for(auto &j : ws3) ca.reloc(j.cref, to);
        }

    // All reasons:
    //
    for(auto &l : trail) {
        Var v = var(l);

        if(reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))) ca.reloc(vardata[v].reason, to);
    }

    trailSaving->reloc(to);


    // All learnt:
    //
    for(CRef &cref : learntsCore) ca.reloc(cref, to);
    for(CRef &cr : learntsTiers) ca.reloc(cr, to);
    for(CRef &cr : learntsLocal) ca.reloc(cr, to);
    for(CRef &uWatch : unaryWatchedClauses) ca.reloc(uWatch, to);

    // All original:
    //
    int i, j;
    for(i = j = 0; i < clauses.size(); i++)
        if(ca[clauses[i]].mark() != 1) {
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);
}


void Solver::garbageCollect() {
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    verbose.log(DEBUGVERBOSE, "|  Garbage collection:   %12d bytes => %12d bytes             |\n", ca.size() * ClauseAllocator::Unit_Size,
                to.size() * ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
