#ifndef GLUCOSE_REDUCE_H
#define GLUCOSE_REDUCE_H

#include "Solver.h"
#include "SolverTypes.h"

namespace Glucose {

class Solver;

enum ClauseManagerType { glucose, tiersclause, tiersclauseSAT20 };

class ClauseManager {
   protected:
    Solver &solver;

   public:
    unsigned long     nbReduced;
    unsigned long     nbRemoved;
    int               factorForPurgatory;
    ClauseManagerType clauseManagerType;   // Avoid dynamic cast...


    ClauseManager(Solver &_solver, int f, ClauseManagerType ct)
        : solver(_solver), nbReduced(0), nbRemoved(0), factorForPurgatory(f), clauseManagerType(ct) { }


    virtual bool triggerReduce() = 0;

    virtual void reduce() = 0;

    virtual void add(CRef cr) = 0;

    virtual bool updateClause(CRef cr, bool duringAnalysis = true) = 0;   // return true if clause is updated

    virtual bool performLCM() = 0;

    virtual void init() { }

    void reducePurgatory();
};


//=================================================================================================
// Glucose Style
//=================================================================================================


class GlucoseClauseManager : public ClauseManager {
    unsigned int specialIncReduceDB;
    unsigned int nbclausesbeforereduce;
    unsigned int curRestart;
    unsigned int lbLBDFrozenClause;
    bool         _performLCM;

   public:
    explicit GlucoseClauseManager(Solver &_solver)
        : ClauseManager(_solver, 2, ClauseManagerType::glucose), specialIncReduceDB(1000), nbclausesbeforereduce(2000),
          curRestart(1), lbLBDFrozenClause(30), _performLCM(true) { }


    bool triggerReduce() override;

    void reduce() override;

    void add(CRef cr) override;

    bool updateClause(CRef cr, bool duringAnalysis) override;

    bool performLCM() override;
};

//=================================================================================================
// Chanseok Oh Style
//=================================================================================================

enum ClauseLocation { core, tiers, local };


class TiersClauseManager : public ClauseManager {
   public:
    unsigned int  nextTiersReduce;
    unsigned int  nextLocalReduce;
    unsigned int  coreUB, tiersUB;
    unsigned long curSimplify, nbconfbeforesimplify;

    explicit TiersClauseManager(Solver &_solver)
        : ClauseManager(_solver, 4, ClauseManagerType::tiersclause), nextTiersReduce(10000), nextLocalReduce(15000), coreUB(3),
          tiersUB(6), curSimplify(1), nbconfbeforesimplify(1000) { }


    bool triggerReduce() override;

    void reduce() override;

    void reduceLocal();

    void reduceTier2();

    void add(CRef cr) override;

    bool updateClause(CRef cr, bool duringAnalysis) override;

    bool performLCM() override;

    void init() override;
};

//=================================================================================================
//  Kochemazov Style - SAT 20 paper
//=================================================================================================

class TiersClauseManagerSAT20 : public TiersClauseManager {
    long coreSizeLimit;

   public:
    explicit TiersClauseManagerSAT20(Solver &_solver) : TiersClauseManager(_solver), coreSizeLimit(50000) {
        clauseManagerType = tiersclauseSAT20;
    }

    bool triggerReduce() override;

    void reduce() override;

    void reduceCore();
};


struct reduceDBAct_lt {
    ClauseAllocator &ca;


    explicit reduceDBAct_lt(ClauseAllocator &ca_) : ca(ca_) { }


    bool operator()(CRef x, CRef y) {
        // Main criteria... Like in MiniSat we keep all binary clauses
        if(ca[x].size() > 2 && ca[y].size() == 2) return true;

        if(ca[y].size() > 2 && ca[x].size() == 2) return false;
        if(ca[x].size() == 2 && ca[y].size() == 2) return false;

        return ca[x].activity() < ca[y].activity();
    }
};

struct reduceDB_lt {
    ClauseAllocator &ca;


    explicit reduceDB_lt(ClauseAllocator &ca_);


    bool operator()(CRef x, CRef y) {
        // Main criteria... Like in MiniSat we keep all binary clauses
        if(ca[x].size() > 2 && ca[y].size() == 2) return true;

        if(ca[y].size() > 2 && ca[x].size() == 2) return false;
        if(ca[x].size() == 2 && ca[y].size() == 2) return false;

        // Second one  based on literal block distance
        if(ca[x].lbd() > ca[y].lbd()) return true;
        if(ca[x].lbd() < ca[y].lbd()) return false;


        // Finally we can use old activity or size, we choose the last one
        return ca[x].activity() < ca[y].activity();
    }
};

// Strategy to reduce unary watches list
struct reduceDB_oneWatched_lt {
    ClauseAllocator &ca;

    explicit reduceDB_oneWatched_lt(ClauseAllocator &ca_);

    bool operator()(CRef x, CRef y) {
        // Main criteria... Like in MiniSat we keep all binary clauses
        if(ca[x].size() > 2 && ca[y].size() == 2) return true;

        if(ca[y].size() > 2 && ca[x].size() == 2) return false;
        if(ca[x].size() == 2 && ca[y].size() == 2) return false;

        // Second one  based on literal block distance
        if(ca[x].size() > ca[y].size()) return true;
        if(ca[x].size() < ca[y].size()) return false;

        if(ca[x].lbd() > ca[y].lbd()) return true;
        if(ca[x].lbd() < ca[y].lbd()) return false;

        // Finally we can use old activity or size, we choose the last one
        return ca[x].activity() < ca[y].activity();
    }
};

struct reduceDB_c {
    ClauseAllocator &ca;
    reduceDB_c(ClauseAllocator &ca_) : ca(ca_) { }
    bool operator()(CRef x, CRef y) const {
        return ((ca[x].lbd() != ca[y].lbd()) && (ca[x].lbd() > ca[y].lbd())) ||
               ((ca[x].lbd() == ca[y].lbd()) && (ca[x].size() > ca[y].size()));
    }
};

}   // namespace Glucose

#endif   // GLUCOSE_REDUCE_H
