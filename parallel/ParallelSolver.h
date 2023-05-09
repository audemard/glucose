//
// Created by audemard on 19/02/2021.
//

#ifndef GLUCOSE_PARALLELSOLVER_H
#define GLUCOSE_PARALLELSOLVER_H


#include <core/Solver.h>
#include <simp/SimpSolver.h>
#include "pfactory/include/Groups.h"
#include "pfactory/include/Communicators.h"

namespace Glucose {
#define SAT   10
#define UNSAT 20
#define UNDEF 0

class ParallelSolver : public Solver {
    vec<SimpSolver*> solvers;
    pFactory::Group* group;
    std::mutex       copyMutex;
    int              winner = -1;

    pFactory::Communicator<int>*       unitsLiteralsCommunicator;
    pFactory::Communicator<vec<Lit>*>* oneWatchCommunicator;
    pFactory::Communicator<vec<Lit>*>* twoWatchCommunicator;

   public:
    lbool solve() override;
    void  displayModel() override;
    void  printStats() override;
    void  createSolvers(SimpSolver* original, unsigned int ncores = 0);
    void  diversify();

    static inline unsigned int lboolToInt(lbool ret) { return ret == l_True ? SAT : (ret == l_False ? UNSAT : UNDEF); }
};
}   // namespace Glucose

#endif   // GLUCOSE_PARALLELSOLVER_H
