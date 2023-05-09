#include "ParallelSolver.h"

#include "core/TargetPhase.h"
#include "pfactory/include/pFactory.h"
#include "utils/System.h"

using namespace Glucose;


lbool ParallelSolver::solve() {
    // Create a group of threads
    group = new pFactory::Group(solvers.size());

    // Add communicators for this group (To use in the solver with send() and recvAll() methods)
    unitsLiteralsCommunicator = new pFactory::Communicator<int>(*group);
    oneWatchCommunicator      = new pFactory::Communicator<vec<Lit>*>(*group);
    twoWatchCommunicator      = new pFactory::Communicator<vec<Lit>*>(*group);

    // Add the tasks for this group using C++11 lambdas
    for(auto solver : solvers) {
        solver->setComponents(group, unitsLiteralsCommunicator, oneWatchCommunicator, twoWatchCommunicator);
        group->add([=]() { return lboolToInt(solver->solve()); });
    }

    pFactory::Controller controller(*group);
    group->concurrent();
    controller.start();
    controller.wait();
    int returnCode = group->getWinner().getReturnCode();
    winner         = group->getWinner().getId();

    return returnCode == SAT ? l_True : (returnCode == UNSAT ? l_False : l_Undef);
}


void ParallelSolver::createSolvers(SimpSolver* original, unsigned int ncores) {
    static double timeBefore = realTime();
    solvers.push(original);   // Add the first one

    original->verbose.log(NORMAL, "c               [Multithreads Solvers Generation]             \n");

    if(ncores == 0) {
        ncores = pFactory::getNbCores();
        original->verbose.log(NORMAL, "c | Number of threads (automatic adjustment) :  %8d       \n", ncores);
    } else
        original->verbose.log(NORMAL, "c | Number of threads (user given option) :  %11d       \n", ncores);

    original->verbose.log(NORMAL, "c | Memory used for one solver :  %19.2f Mb       \n", memUsed());

    double timeTest   = realTime();
    auto*  testSolver = new SimpSolver(*solvers[0]);
    timeTest          = realTime() - timeTest;

    original->verbose.log(NORMAL, "c | Time for one copy:      %20.4f seconds       \n", timeTest);
    timeTest *= ncores;
    original->verbose.log(NORMAL, "c | Simulation copy time:   %20.4f seconds       \n", timeTest);
    solvers.push(testSolver);

    if(timeTest > 1) {
        // Create a group of threads :) n-2 remaining copies
        auto* g1 = new pFactory::Group(ncores - 2);

        printf("c | Parallel copy :)\n");
        for(unsigned int i = 2; i < ncores; i++) {
            g1->add([=]() {
                auto* solver = new SimpSolver(*solvers[0]);
                copyMutex.lock();
                solvers.push(solver);
                copyMutex.unlock();
                return 0;
            });
        }
        g1->start();
        g1->wait();
    } else {
        original->verbose.log(NORMAL, "c | Sequential copy :)\n");
        for(unsigned int i = 2; i < ncores; i++) solvers.push(new SimpSolver(*solvers[0]));
    }


    original->verbose.log(NORMAL, "c | Copy time:              %20.4f seconds       \n", realTime() - timeBefore);
    original->verbose.log(NORMAL, "c | Memory used for all solvers :  %18.2f Mb       \n", memUsed());
    original->verbose.log(
        NORMAL, "c =========================================================================================================\n");

    original->verbose.log(NORMAL, "c display only trace for solver 0\n");

    for(int i = 1; i < solvers.size(); i++) solvers[i]->verbose.verbosity = -1;

    diversify();
}


void ParallelSolver::diversify() {
    // Solver 1 is a glucose like solver
    solvers[1]->restart       = solvers[1]->glucoseRestart;
    solvers[1]->searchMode    = SearchMode::onlyFocus;
    solvers[1]->clauseManager = new GlucoseClauseManager(*solvers[1]);


    if(solvers[0]->walkMode && solvers[0]->nVars() < solvers[0]->targetPhase->maxVariablesForWalker)
        solvers[2]->targetPhase->createSequence("OB WB IB WB RB F");
    else
        solvers[2]->targetPhase->createSequence("OB IB RB F");

    if(solvers.size() >= 7){
        if(solvers[0]->walkMode && solvers[0]->nVars() < solvers[0]->targetPhase->maxVariablesForWalker)
            solvers[6]->targetPhase->createSequence("IB WB OB WB RB F");
        else
            solvers[6]->targetPhase->createSequence("IB OB RB F");
    }


    // Randomize first descent for all except first solver
    for(int i = 1; i < solvers.size(); i++) {
        solvers[i]->randomizeFirstDescent = true;
        solvers[i]->random_seed           = solvers[0]->random_seed * (i + 1);
        solvers[i]->random.setSeed(solvers[i]->random_seed);
    }
}


void ParallelSolver::displayModel() { solvers[winner]->displayModel(); }


void ParallelSolver::printStats() {
    SimpSolver* original = solvers[0];

    original->verbose.log(
        NORMAL, "c =========================================================================================================\n");
    original->verbose.log(NORMAL, "c |                       [Communicators]                      \n");
    original->verbose.log(NORMAL, "c | Communicators: UnitLiterals - %s\n",
                          unitsLiteralsCommunicator == nullptr ? "Disabled" : "Enabled");
    if(unitsLiteralsCommunicator)
        original->verbose.log(NORMAL, "c | Communicators: UnitLiterals - %d sent - %d received\n",
                              unitsLiteralsCommunicator->getNbSend(), unitsLiteralsCommunicator->getNbRecv());
    original->verbose.log(NORMAL, "c | Communicators: twoWatchCommunicator - %s\n",
                          twoWatchCommunicator == nullptr ? "Disabled" : "Enabled");
    if(twoWatchCommunicator)
        original->verbose.log(NORMAL, "c | Communicators: twoWatchCommunicator - %d sent - %d received\n",
                              twoWatchCommunicator->getNbSend(), twoWatchCommunicator->getNbRecv());
    original->verbose.log(NORMAL, "c | Communicators: oneWatchCommunicator - %s\n",
                          oneWatchCommunicator == nullptr ? "Disabled" : "Enabled");
    if(oneWatchCommunicator)
        original->verbose.log(NORMAL, "c | Communicators: oneWatchCommunicator - %d sent - %d received\n",
                              oneWatchCommunicator->getNbSend(), oneWatchCommunicator->getNbRecv());
    original->verbose.log(
        NORMAL, "c =========================================================================================================\n");


    if(winner != -1) {
        solvers[0]->verbose.log(NORMAL, "c winner is solver %d\n", winner);
        solvers[winner]->verbose.verbosity = solvers[0]->verbose.verbosity;
        solvers[winner]->printStats();
    } else
        solvers[0]->printStats();
}