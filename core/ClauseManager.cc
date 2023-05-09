#include "ClauseManager.h"

#include <mtl/Sort.h>

#include "Solver.h"
#include "SolverTypes.h"
#include "TrailSaving.h"
using namespace Glucose;


void ClauseManager::reducePurgatory() {
    int              i, j;
    int              limit               = solver.unaryWatchedClauses.size() - (solver.learntsCore.size() * factorForPurgatory);
    ClauseAllocator &ca                  = solver.ca;
    vec<CRef> &      unaryWatchedClauses = solver.unaryWatchedClauses;
    if((unaryWatchedClauses.size() > 100) && (limit > 0)) {
        sort(unaryWatchedClauses, reduceDB_oneWatched_lt(solver.ca));

        for(i = j = 0; i < unaryWatchedClauses.size(); i++) {
            Clause &c = ca[unaryWatchedClauses[i]];
            if(c.lbd() > 2 && c.size() > 2 && c.canbedel() && !solver.locked(c) && (i < limit)) {
                solver.removeClause(unaryWatchedClauses[i], c.oneWatched());   // remove from the purgatory (or not)
                solver.parallelStats[nbRemovedInPurgatory]++;
            } else {
                if(!c.canbedel()) limit++;   // we keep c, so we can delete an other clause
                c.canbedel(true);            // At the next step, c can be delete
                unaryWatchedClauses[j++] = unaryWatchedClauses[i];
            }
        }
        unaryWatchedClauses.shrink(i - j);
    }
}
//=================================================================================================
// Glucose Style
//=================================================================================================


void GlucoseClauseManager::add(CRef cr) { solver.learntsCore.push(cr); }


bool GlucoseClauseManager::triggerReduce() {
    if(solver.conflicts >= (curRestart * nbclausesbeforereduce) && solver.learntsCore.size() > 0) {
        curRestart = (solver.conflicts / nbclausesbeforereduce) + 1;
        return true;
    }
    return false;
}


void GlucoseClauseManager::reduce() {
    solver.verbose.log(DEBUGVERBOSE, "%-12" PRIu64 " conflicts: Reduce DB\n", solver.conflicts);
    _performLCM = true;
    solver.trailSaving->reset();


    int i, j;
    nbReduced++;
    vec<CRef> &      learnts = solver.learntsCore;
    ClauseAllocator &ca      = solver.ca;
    sort(learnts, reduceDBAct_lt(solver.ca));


    sort(learnts, reduceDB_lt(ca));

    // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
    if(ca[learnts[learnts.size() / 2]].lbd() <= 3) nbclausesbeforereduce += specialIncReduceDB;
    // Useless :-)
    if(ca[learnts.last()].lbd() <= 5) nbclausesbeforereduce += specialIncReduceDB;


    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

    int limit = (learnts.size() / 2);   //

    for(i = j = 0; i < learnts.size(); i++) {
        Clause &c = ca[learnts[i]];
        if(c.lbd() > 2 && c.size() > 2 && c.canbedel() && !solver.locked(c) && (i < limit)) {
            solver.removeClause(learnts[i]);
            nbRemoved++;
        } else {
            if(!c.canbedel()) limit++;   // we keep c, so we can delete an other clause
            c.canbedel(true);            // At the next step, c can be delete
            learnts[j++] = learnts[i];
        }
    }
    learnts.shrink(i - j);

    if(solver.unaryWatchedClauses.size() > 0) reducePurgatory();

    solver.checkGarbage();
}


bool GlucoseClauseManager::updateClause(CRef cr, bool duringAnalysis) {
    Clause &c = solver.ca[cr];
    solver.claBumpActivity(c);
    if(c.lbd() > 2) {
        unsigned int lbd = solver.computeLBD(c);
        if(lbd + 1 < c.lbd()) {                                                     // improve the LBD
            if(c.lbd() <= lbLBDFrozenClause && duringAnalysis) c.canbedel(false);   // seems to be interesting
            c.lbd(lbd);                                                             // Update it
            return true;
        }
    }
    return false;
}


bool GlucoseClauseManager::performLCM() {
    if(_performLCM) {
        _performLCM = false;
        return true;
    }
    return false;
}

//=================================================================================================
// 3 tiers Style
//=================================================================================================


bool TiersClauseManager::triggerReduce() { return solver.conflicts >= nextTiersReduce || solver.conflicts >= nextLocalReduce; }


void TiersClauseManager::reduce() {
    nbReduced++;
    solver.trailSaving->reset();

    if(solver.conflicts >= nextTiersReduce) {
        nextTiersReduce = solver.conflicts + 10000;
        reduceTier2();
    }
    if(solver.conflicts >= nextLocalReduce) {
        nextLocalReduce = solver.conflicts + 15000;
        reduceLocal();
    }

    if(solver.unaryWatchedClauses.size() > 0) reducePurgatory();

    solver.checkGarbage();
}


void TiersClauseManager::reduceTier2() {
    int              i, j;
    vec<CRef> &      learnts_tiers = solver.learntsTiers;
    ClauseAllocator &ca            = solver.ca;
    for(i = j = 0; i < learnts_tiers.size(); i++) {
        Clause &c = ca[learnts_tiers[i]];
        if(c.location() == ClauseLocation::tiers) {
            if(!solver.locked(c) && c.touched() + 30000 < solver.conflicts) {
                solver.learntsLocal.push(learnts_tiers[i]);
                c.location(ClauseLocation::local);
                c.activity() = 0;
                solver.claBumpActivity(c);
            } else
                learnts_tiers[j++] = learnts_tiers[i];
        }
    }
    learnts_tiers.shrink(i - j);
}


void TiersClauseManager::reduceLocal() {
    int i, j;

    vec<CRef> &      learnts_local = solver.learntsLocal;
    ClauseAllocator &ca            = solver.ca;
    sort(learnts_local, reduceDB_lt(ca));

    int limit = learnts_local.size() / 2;
    for(i = j = 0; i < learnts_local.size(); i++) {
        Clause &c = ca[learnts_local[i]];
        if(c.location() == ClauseLocation::local) {
            if(c.canbedel() && !solver.locked(c) && i < limit) {
                solver.removeClause(learnts_local[i]);
                nbRemoved++;
            } else {
                if(!c.canbedel()) limit++;
                c.canbedel(true);
                learnts_local[j++] = learnts_local[i];
            }
        }
    }
    learnts_local.shrink(i - j);
}


void TiersClauseManager::add(CRef cr) {
    Clause &c = solver.ca[cr];
    if(c.lbd() <= coreUB) {
        solver.learntsCore.push(cr);
        c.location(ClauseLocation::core);
    } else if(c.lbd() <= tiersUB) {
        solver.learntsTiers.push(cr);
        c.location(ClauseLocation::tiers);
        c.touched() = solver.conflicts;
    } else {
        c.location(ClauseLocation::local);
        solver.learntsLocal.push(cr);
    }
    if(solver.conflicts == 100000 && solver.learntsCore.size() < 100) coreUB = 5;
}


bool TiersClauseManager::updateClause(CRef cr, bool duringAnalysis) {
    Clause &c = solver.ca[cr];
    if(c.learnt() && c.location() != ClauseLocation::core) {
        unsigned int lbd = solver.computeLBD(c);
        if(lbd < c.lbd()) {
            if(c.lbd() <= 30 && duringAnalysis) c.canbedel(false);   // Protect once from reduction.
            c.lbd(lbd);
            if(lbd <= coreUB) {
                solver.learntsCore.push(cr);
                c.location(ClauseLocation::core);
            } else if(lbd <= tiersUB && c.location() == ClauseLocation::local) {
                solver.learntsTiers.push(cr);
                c.location(ClauseLocation::tiers);
            }
        }

        if(duringAnalysis) {
            if(c.location() == ClauseLocation::tiers)
                c.touched() = solver.conflicts;
            else if(c.location() == ClauseLocation::local)
                solver.claBumpActivity(c);
        }
    }

    return false;
}

bool TiersClauseManager::performLCM() {
    if(solver.conflicts >= curSimplify * nbconfbeforesimplify) {
        curSimplify = (solver.conflicts / nbconfbeforesimplify) + 1;
        nbconfbeforesimplify += 1000;
        return true;
    }
    return false;
}


void TiersClauseManager::init() { nextLocalReduce = solver.conflicts + 15000; }

reduceDB_lt::reduceDB_lt(ClauseAllocator &ca_) : ca(ca_) { }


reduceDB_oneWatched_lt::reduceDB_oneWatched_lt(ClauseAllocator &ca_) : ca(ca_) { }

//=================================================================================================
//  Kochemazov Style - SAT 20 paper
//=================================================================================================

void TiersClauseManagerSAT20::reduceCore() {
    int              i, j;
    ClauseAllocator &ca = solver.ca;
    printf("Core size before reduce: %i\n", solver.learntsCore.size());

    sort(solver.learntsCore, reduceDB_c(ca));
    int limit = solver.learntsCore.size() / 2;

    for(i = j = 0; i < solver.learntsCore.size(); i++) {
        Clause &c = ca[solver.learntsCore[i]];
        if(c.mark() == ClauseLocation::core) {
            if(c.lbd() > 2 && !solver.locked(c) && (c.touched() + 100000 < solver.conflicts) && i < limit) {
                solver.learntsTiers.push(solver.learntsCore[i]);
                c.mark(ClauseLocation::tiers);
                c.touched() = solver.conflicts;
            } else {
                solver.learntsCore[j++] = solver.learntsCore[i];
                if(solver.locked(c) || (c.touched() + 50000 < solver.conflicts) || c.lbd() <= 2) limit++;
            }
        }
    }
    solver.learntsCore.shrink(i - j);
    printf("Core size after reduce: %i\n", solver.learntsCore.size());
}

bool TiersClauseManagerSAT20::triggerReduce() {
    return TiersClauseManager::triggerReduce() || solver.learntsCore.size() > coreSizeLimit;
}


void TiersClauseManagerSAT20::reduce() {
    if(solver.learntsCore.size() > coreSizeLimit) {
        reduceCore();
        coreSizeLimit += coreSizeLimit / 10;
    }

    TiersClauseManager::reduce();
}
