#include "ClauseManager.h"
#include "Solver.h"
#include "TrailSaving.h"
#include "mtl/Sort.h"

using namespace Glucose;


// simplify All
//
CRef Solver::simplePropagate() {
    CRef confl     = CRef_Undef;
    int  num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    while(qhead < trail.size()) {
        Lit           p  = trail[qhead++];   // 'p' is enqueued fact to propagate.
        vec<Watcher> &ws = watches[p];
        Watcher *     i, *j, *end;
        num_props++;

        // First, Propagate binary clauses
        vec<Watcher> &wbin = watchesBin[p];

        for(auto &binWatch : wbin) {
            Lit imp = binWatch.blocker;

            if(value(imp) == l_False) return binWatch.cref;

            if(value(imp) == l_Undef) simpleUncheckEnqueue(imp, binWatch.cref);
        }

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
            //  i++;

            // If 0th watch is true, then clause is already satisfied.
            // However, 0th watch is not the blocker, make it blocker using a new watcher w
            // why not simply do i->blocker=first in this case?
            Lit first = c[0];
            //  Watcher w     = Watcher(cr, first);
            if(first != blocker && value(first) == l_True) {
                i->blocker = first;
                *j++       = *i++;
                continue;
            }

            for(int k = 2; k < c.size(); k++) {
                if(value(c[k]) != l_False) {
                    // watcher i is abandonned using i++, because cr watches now ~c[k] instead of p
                    // the blocker is first in the watcher. However,
                    // the blocker in the corresponding watcher in ~first is not c[1]
                    Watcher w = Watcher(cr, first);
                    i++;
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }
            }


            // Did not find watch -- clause is unit under assignment:
            i->blocker = first;
            *j++       = *i++;
            if(value(first) == l_False) {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while(i < end) *j++ = *i++;
            } else {
                simpleUncheckEnqueue(first, cr);
            }
        NextClause:;
        }
        ws.shrink(i - j);
    }
    return confl;
}


void Solver::simpleUncheckEnqueue(Lit p, CRef from) {
    assert(value(p) == l_Undef);
    assigns[var(p)]        = lbool(!sign(p));   // this makes a lbool object whose value is sign(p)
    vardata[var(p)].reason = from;
    trail.push_(p);
}


void Solver::cancelUntilTrailRecord() {
    for(int c = trail.size() - 1; c >= trailRecord; c--) {
        Var x      = var(trail[c]);
        assigns[x] = l_Undef;
    }
    qhead = trailRecord;
    trail.shrink(trail.size() - trailRecord);
}


void Solver::litsEnqueue(int cutP, Clause &c) {
    for(int i = cutP; i < c.size(); i++) {
        simpleUncheckEnqueue(~c[i]);
    }
}


bool Solver::removed(CRef cr) { return ca[cr].mark() == 1; }


void Solver::simpleAnalyze(CRef confl, vec<Lit> &out_learnt, vec<CRef> &reason_clause, bool True_confl) {
    int pathC = 0;
    Lit p     = lit_Undef;
    int index = trail.size() - 1;

    do {
        if(confl != CRef_Undef) {
            reason_clause.push(confl);
            Clause &c = ca[confl];
            // Special case for binary clauses
            // The first one has to be SAT
            if(p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {
                assert(value(c[1]) == l_True);
                Lit tmp = c[0];
                c[0] = c[1], c[1] = tmp;
            }
            // if True_confl==true, then choose p begin with the 1th index of c;
            for(int j = (p == lit_Undef && True_confl == false) ? 0 : 1; j < c.size(); j++) {
                Lit q = c[j];
                if(!seen[var(q)]) {
                    seen[var(q)]=  1;
                    pathC++;
                }
            }
        } else
            out_learnt.push(~p);

        // if not break, while() will come to the index of trail blow 0, and fatal error occur;
        if(pathC == 0) break;
        // Select next clause to look at:
        while(!seen[var(trail[index--])])
            ;
        // if the reason cr from the 0-level assigned var, we must break avoid move forth further;
        // but attention that maybe seen[x]=1 and never be clear. However makes no matter;
        if(trailRecord > index + 1) break;
        p     = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while(pathC >= 0);
}


void Solver::simplifyLearnt(CRef cr) {
    Clause &c = ca[cr];
    stats[lcmTested]++;

    trailRecord = trail.size();   // record the start pointer

    vec<Lit> falseLit;

    falseLit.clear();

    bool True_confl = false;
    int  i, j;
    CRef confl;

    for(i = 0, j = 0; i < c.size(); i++) {
        if(value(c[i]) == l_Undef) {
            simpleUncheckEnqueue(~c[i]);
            c[j++] = c[i];
            confl  = simplePropagate();
            if(confl != CRef_Undef) {
                break;
            }
        } else {
            if(value(c[i]) == l_True) {
                c[j++]     = c[i];
                True_confl = true;
                confl      = reason(var(c[i]));
                break;
            } else {
                falseLit.push(c[i]);
            }
        }
    }
    c.shrink(c.size() - j);
    if(LCMUpdateLBD && ((int)c.lbd()) > c.size()) c.lbd(c.size());

    if(confl != CRef_Undef || True_confl == true) {
        simp_learnt_clause.clear();
        simp_reason_clause.clear();
        if(True_confl == true) simp_learnt_clause.push(c.last());

        simpleAnalyze(confl, simp_learnt_clause, simp_reason_clause, True_confl);

        if(simp_learnt_clause.size() < c.size()) {
            for(i = 0; i < simp_learnt_clause.size(); i++) {
                c[i] = simp_learnt_clause[i];
            }
            c.shrink(c.size() - i);
            /*
             * Seems to be better when not activated
             * if(LCMUpdateLBD && (clauseManager->clauseManagerType == ClauseManagerType::glucose ||
                                (clauseManager->clauseManagerType == ClauseManagerType::chanseokoh && c.location() ==
            ClauseLocation::tiers))) { clauseManager->updateClause(cr, false);
            }*/
        }
    }

    cancelUntilTrailRecord();
}


bool Solver::simplifySetOfLearnts(vec<CRef> &learnts) {
    int      beforeSize, afterSize;
    int      ci, cj, li, lj;
    bool     sat, false_lit;
    vec<Lit> ori_c;


    if(clauseManager->clauseManagerType == ClauseManagerType::glucose) sort(learnts, reduceDB_lt(ca));

    for(ci = 0, cj = 0; ci < learnts.size(); ci++) {
        CRef    cr = learnts[ci];
        Clause &c  = ca[cr];

        if(removed(cr) || c.imported()) continue;


        sat = false_lit = false;
        for(int i = 0; i < c.size(); i++) {
            if(value(c[i]) == l_True) {
                sat = true;
                break;
            } else if(value(c[i]) == l_False)
                false_lit = true;
        }
        if(sat) {
            removeClause(cr);
        } else {
            detachClause(cr, true);

            if(false_lit) {
                for(li = lj = 0; li < c.size(); li++) {
                    if(value(c[li]) != l_False) c[lj++] = c[li];
                }
                c.shrink(li - lj);
                if(certifiedUNSAT) addToDrat(c, true);
            }
            ////
            if(ci < learnts.size() / 2 || c.simplified()) {
                attachClause(cr);
                learnts[cj++] = learnts[ci];
                continue;
            }

            beforeSize = c.size();
            assert(c.size() > 1);
            // simplify a learnt clause c
            simplifyLearnt(cr);
            assert(c.size() > 0);
            afterSize = c.size();

            if(beforeSize > afterSize) {
                if(certifiedOutput) addToDrat(c, true);
                stats[lcmReduced]++;
            }

            if(c.size() == 1) {
                // when unit clause occur, enqueue and propagate
                uncheckedEnqueue(c[0]);
                if(propagate() != CRef_Undef) {
                    ok = false;
                    return false;
                }
                // delete the clause memory in logic
                c.mark(1);
                ca.free(cr);
            } else {
                attachClause(cr);
                learnts[cj++] = learnts[ci];
                if(LCMUpdateLBD && (clauseManager->clauseManagerType == ClauseManagerType::glucose ||
                                    (clauseManager->clauseManagerType == ClauseManagerType::tiersclause &&
                                     c.location() == ClauseLocation::tiers))) {
                    clauseManager->updateClause(cr, false);
                }
                c.simplified(true);
            }
        }
    }
    learnts.shrink(ci - cj);

    return true;
}


bool Solver::simplifyAll() {
    trailSaving->reset();

    if(!ok || propagate() != CRef_Undef) return ok = false;

    removeSatisfied(clauses);

    int i, j;

    if(simplifySetOfLearnts(learntsCore) == false) return false;


    if(simplifySetOfLearnts(learntsTiers) == false) return false;


    for(i = j = 0; i < learntsCore.size(); i++)
        if(ca[learntsCore[i]].mark() != 1) learntsCore[j++] = learntsCore[i];
    learntsCore.shrink(i - j);

    for(i = j = 0; i < learntsTiers.size(); i++)
        if(ca[learntsTiers[i]].mark() != 1) learntsTiers[j++] = learntsTiers[i];
    learntsTiers.shrink(i - j);

    for(i = j = 0; i < learntsLocal.size(); i++)
        if(ca[learntsLocal[i]].mark() != 1) learntsLocal[j++] = learntsLocal[i];
    learntsLocal.shrink(i - j);

    checkGarbage();

    return true;
}
