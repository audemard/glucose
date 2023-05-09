#include "Solver.h"
#include "mtl/Sort.h"
using namespace Glucose;



// simplify All
//
CRef Solver::simplePropagate()
{
    CRef    confl = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    while (qhead < trail.size()){
        Lit            p = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        // First, Propagate binary clauses
        vec<Watcher>&  wbin = watchesBin[p];

        for (int k = 0; k<wbin.size(); k++){

            Lit imp = wbin[k].blocker;

            if (value(imp) == l_False){
                return wbin[k].cref;
            }

            if (value(imp) == l_Undef){
                simpleUncheckEnqueue(imp, wbin[k].cref);
            }
        }
        for (i = j = (Watcher*)ws, end = i + ws.size(); i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue;
            }

            // Make sure the false literal is data[1]:
            CRef     cr = i->cref;
            Clause&  c = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            //  i++;

            // If 0th watch is true, then clause is already satisfied.
            // However, 0th watch is not the blocker, make it blocker using a new watcher w
            // why not simply do i->blocker=first in this case?
            Lit     first = c[0];
            //  Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                i->blocker = first;
                *j++ = *i++; continue;
            }

            // Look for new watch:
            if (incremental){ // ----------------- INCREMENTAL MODE
                int choosenPos = -1;
                for (int k = 2; k < c.size(); k++){
                    if (value(c[k]) != l_False){
                        if (decisionLevel()>assumptions.size()){
                            choosenPos = k;
                            break;
                        }
                        else{
                            choosenPos = k;

                            if (value(c[k]) == l_True || !isSelector(var(c[k]))) {
                                break;
                            }
                        }

                    }
                }
                if (choosenPos != -1){
                    // watcher i is abandonned using i++, because cr watches now ~c[k] instead of p
                    // the blocker is first in the watcher. However,
                    // the blocker in the corresponding watcher in ~first is not c[1]
                    Watcher w = Watcher(cr, first); i++;
                    c[1] = c[choosenPos]; c[choosenPos] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }
            }
            else{  // ----------------- DEFAULT  MODE (NOT INCREMENTAL)
                for (int k = 2; k < c.size(); k++){

                    if (value(c[k]) != l_False){
                        // watcher i is abandonned using i++, because cr watches now ~c[k] instead of p
                        // the blocker is first in the watcher. However,
                        // the blocker in the corresponding watcher in ~first is not c[1]
                        Watcher w = Watcher(cr, first); i++;
                        c[1] = c[k]; c[k] = false_lit;
                        watches[~c[1]].push(w);
                        goto NextClause;
                    }
                }
            }

            // Did not find watch -- clause is unit under assignment:
            i->blocker = first;
            *j++ = *i++;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }
            else{
                simpleUncheckEnqueue(first, cr);
            }
            NextClause:;
        }
        ws.shrink(i - j);

        // unaryWatches "propagation"
        if(useUnaryWatched && confl == CRef_Undef) {
            confl = simplePropagateUnaryWatches(p);

        }
    }


    return confl;
}

CRef Solver::simplePropagateUnaryWatches(Lit p) {
    CRef confl = CRef_Undef;
    Watcher *i, *j, *end;
    vec <Watcher> &ws = unaryWatches[p];
    for(i = j = (Watcher *) ws, end = i + ws.size(); i != end;) {
        // Try to avoid inspecting the clause:
        Lit blocker = i->blocker;
        if(value(blocker) == l_True) {
            *j++ = *i++;
            continue;
        }

        // Make sure the false literal is data[1]:
        CRef cr = i->cref;
        Clause &c = ca[cr];
        assert(c.getOneWatched());
        Lit false_lit = ~p;
        assert(c[0] == false_lit); // this is unary watch... No other choice if "propagated"
        //if (c[0] == false_lit)
        //c[0] = c[1], c[1] = false_lit;
        //assert(c[1] == false_lit);
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
        while(i < end)
            *j++ = *i++;

        NextClauseUnary:;
    }
    ws.shrink(i - j);

    return confl;
}


void Solver::simpleUncheckEnqueue(Lit p, CRef from){
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p)); // this makes a lbool object whose value is sign(p)
    vardata[var(p)].reason = from;
    trail.push_(p);
}

void Solver::cancelUntilTrailRecord()
{
    for (int c = trail.size() - 1; c >= trailRecord; c--)
    {
        Var x = var(trail[c]);
        assigns[x] = l_Undef;

    }
    qhead = trailRecord;
    trail.shrink(trail.size() - trailRecord);

}

void Solver::litsEnqueue(int cutP, Clause& c)
{
    for (int i = cutP; i < c.size(); i++)
    {
        simpleUncheckEnqueue(~c[i]);
    }
}

bool Solver::removed(CRef cr) {
    return ca[cr].mark() == 1;
}

void Solver::simpleAnalyze(CRef confl, vec<Lit>& out_learnt, vec<CRef>& reason_clause, bool True_confl)
{
    int pathC = 0;
    Lit p = lit_Undef;
    int index = trail.size() - 1;

    do{
        if (confl != CRef_Undef){
            reason_clause.push(confl);
            Clause& c = ca[confl];
            // Special case for binary clauses
            // The first one has to be SAT
            if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {

                assert(value(c[1]) == l_True);
                Lit tmp = c[0];
                c[0] = c[1], c[1] = tmp;
            }
            // if True_confl==true, then choose p begin with the 1th index of c;
            for (int j = (p == lit_Undef && True_confl == false) ? 0 : 1; j < c.size(); j++){
                Lit q = c[j];
                if (!seen[var(q)]){
                    seen[var(q)] = 1;
                    pathC++;
                }
            }
        }
        else if (confl == CRef_Undef){
            out_learnt.push(~p);
        }
        // if not break, while() will come to the index of trail blow 0, and fatal error occur;
        if (pathC == 0) break;
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        // if the reason cr from the 0-level assigned var, we must break avoid move forth further;
        // but attention that maybe seen[x]=1 and never be clear. However makes no matter;
        if (trailRecord > index + 1) break;
        p = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC >= 0);
}

void Solver::simplifyLearnt(Clause& c)
{
    stats[lcmtested]++;

    trailRecord = trail.size();// record the start pointer

    vec<Lit> falseLit;

    falseLit.clear();

    bool True_confl = false;
    int beforeSize, afterSize;
    beforeSize = c.size();
    int i, j;
    CRef confl;

    for (i = 0, j = 0; i < c.size(); i++){
        if (value(c[i]) == l_Undef){
            //printf("///@@@ uncheckedEnqueue:index = %d. l_Undef\n", i);
            simpleUncheckEnqueue(~c[i]);
            c[j++] = c[i];
            confl = simplePropagate();
            if (confl != CRef_Undef){
                break;
            }
        }
        else{
            if (value(c[i]) == l_True){
                //printf("///@@@ uncheckedEnqueue:index = %d. l_True\n", i);
                c[j++] = c[i];
                True_confl = true;
                confl = reason(var(c[i]));
                break;
            }
            else{
                falseLit.push(c[i]);
                //printf("///@@@ uncheckedEnqueue:index = %d. l_False\n", i);
            }
        }
    }
    c.shrink(c.size() - j);
    if (LCMUpdateLBD && c.lbd() > c.size()) c.setLBD(c.size());
    afterSize = c.size();

    if (confl != CRef_Undef || True_confl == true){
        simp_learnt_clause.clear();
        simp_reason_clause.clear();
        if (True_confl == true){
            simp_learnt_clause.push(c.last());
        }
        simpleAnalyze(confl, simp_learnt_clause, simp_reason_clause, True_confl);

        if (simp_learnt_clause.size() < c.size()){
            for (i = 0; i < simp_learnt_clause.size(); i++){
                c[i] = simp_learnt_clause[i];
            }
            c.shrink(c.size() - i);
            if (LCMUpdateLBD) {
                int nblevels = computeLBD(simp_learnt_clause);
                if (nblevels < c.lbd())
                    c.setLBD(nblevels);
            }
        }
    }

    cancelUntilTrailRecord();

}

bool Solver::simplifyAll()
{
    int nbGoodReduce = 0;
    int beforeSize, afterSize;
    int nbSize1 = 0, nbSize2 = 0;

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    removeSatisfied(clauses);

    int ci, cj, li, lj;
    bool sat, false_lit;
    unsigned int nblevels;
    vec<Lit> ori_c;

    if (0 && chanseokStrategy && permanentLearnts.size() > 0) {
        for (ci = 0, cj = 0; ci < permanentLearnts.size(); ci++){
            CRef cr = permanentLearnts[ci];
            Clause& c = ca[cr];

            if (!removed(cr)){
                sat = false_lit = false;
                for (int i = 0; i < c.size(); i++){
                    if (value(c[i]) == l_True){
                        sat = true;
                        break;
                    }
                    else if (value(c[i]) == l_False){
                        false_lit = true;
                    }
                }
                if (sat){
                    removeClause(cr);
                }
                else{
                    detachClause(cr, true);

                    if (false_lit){
                        for (li = lj = 0; li < c.size(); li++){
                            if (value(c[li]) != l_False){
                                c[lj++] = c[li];
                            }
                        }
                        c.shrink(li - lj);
                        if(certifiedUNSAT)
                            addToDrat(c, true);
                    }
                    ////
                    if (c.simplified() || c.lbd() > 3) {
                        attachClause(cr);
                        permanentLearntsReduced.push(cr); //[cj++] = permanentLearnts[ci];
                        // permanentLearnts[cj++] = permanentLearnts[ci];
                        continue;
                    }

                    beforeSize = c.size();
                    assert(c.size() > 1);
                    // simplify a learnt clause c
                    simplifyLearnt(c);
                    assert(c.size() > 0);
                    afterSize = c.size();

                    if (beforeSize > afterSize){
                        if (afterSize <= 3) {
                            nbGoodReduce++;
                            if (afterSize > 1) parallelExportClauseDuringSearch(c);
                            if (afterSize == 2){
                                nbSize2++;
                            }
                        }
                        if(certifiedOutput)
                            addToDrat(c, true);
                        stats[lcmreduced]++;
                    }

                    if (c.size() == 1){
                        nbSize1++;
                        // when unit clause occur, enqueue and propagate
                        uncheckedEnqueue(c[0]);
                        parallelExportUnaryClause(c[0]);
                        if (propagate() != CRef_Undef)
                        {
                            ok = false;
                            return false;
                        }
                        // delete the clause memory in logic
                        c.mark(1);
                        ca.free(cr);
                    }
                    else{
                        attachClause(cr);
                        permanentLearntsReduced.push(cr); //[cj++] = permanentLearnts[ci];
                        //permanentLearnts[cj++] = permanentLearnts[ci];
                        // TODO
                        /*nblevels = computeLBD(c);
                          if (nblevels < c.lbd()){
                          c.setLBD(nblevels);
                          }*/

                        c.setSimplified(true);
                    }
                }
            }
        }
        permanentLearnts.shrink(ci - cj);
    }

    if (!chanseokStrategy) {
        sort(learnts, reduceDB_lt(ca));

        for (ci = 0, cj = 0; ci < learnts.size(); ci++){
            CRef cr = learnts[ci];
            Clause& c = ca[cr];

            if (!removed(cr)){
                sat = false_lit = false;
                for (int i = 0; i < c.size(); i++){
                    if (value(c[i]) == l_True){
                        sat = true;
                        break;
                    }
                    else if (value(c[i]) == l_False){
                        false_lit = true;
                    }
                }
                if (sat){
                    removeClause(cr);
                }
                else{
                    detachClause(cr, true);

                    if (false_lit){
                        for (li = lj = 0; li < c.size(); li++){
                            if (value(c[li]) != l_False){
                                c[lj++] = c[li];
                            }
                        }
                        c.shrink(li - lj);
                        if(certifiedUNSAT)
                            addToDrat(c, true);
                    }
                    ////
                    if (ci < learnts.size() / 2 || c.simplified()) {
                        attachClause(cr);
                        learnts[cj++] = learnts[ci];
                        continue;
                    }

                    beforeSize = c.size();
                    assert(c.size() > 1);
                    // simplify a learnt clause c
                    simplifyLearnt(c);
                    assert(c.size() > 0);
                    afterSize = c.size();

                    if (beforeSize > afterSize){
                        if (afterSize <= 3) {
                            nbGoodReduce++;
                            if (afterSize > 1) parallelExportClauseDuringSearch(c);
                            if (afterSize == 2){
                                nbSize2++;
                            }
                        }
                        if(certifiedOutput)
                            addToDrat(c, true);
                        stats[lcmreduced]++;
                    }

                    if (c.size() == 1){
                        nbSize1++;
                        // when unit clause occur, enqueue and propagate
                        uncheckedEnqueue(c[0]);
                        parallelExportUnaryClause(c[0]);
                        if (propagate() != CRef_Undef)
                        {
                            ok = false;
                            return false;
                        }
                        // delete the clause memory in logic
                        c.mark(1);
                        ca.free(cr);
                    }
                    else{
                        attachClause(cr);
                        learnts[cj++] = learnts[ci];
                        // TODO
                        /*nblevels = computeLBD(c);
                          if (nblevels < c.lbd()){
                          c.setLBD(nblevels);
                          }*/

                        c.setSimplified(true);
                    }
                }
            }
        }
        learnts.shrink(ci - cj);
    }

    checkGarbage();

    return true;
}



