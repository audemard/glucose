//
// Created by audemard on 14/10/2020.
//

#ifndef GLUCOSE_TARGETPHASE_H
#define GLUCOSE_TARGETPHASE_H

#include "CCANR.h"
#include "Solver.h"

namespace Glucose {
enum phase { best, flipped, original, inverted, random, walk };

class TargetPhase {
    Solver &     solver;
    unsigned int nextRephasing;
    unsigned int sizeBestPhase;
    unsigned int sizeBestofthePhase, minSize;
    unsigned int nbRephasing;
    vec<phase>   cycle;
    vec<char>    bestPolarity;

   public:
    int   maxVariablesForWalker;
    CCANR ccanr;


    TargetPhase(Solver &_s)
        : solver(_s), nextRephasing(1000), sizeBestPhase(0), sizeBestofthePhase(0), minSize(0), nbRephasing(0),
          maxVariablesForWalker(70000), ccanr(_s) { }


    inline void initialize() {
        bestPolarity.growTo(solver.nVars());
        minSize = solver.nVars();

        if(cycle.size() > 0)   // cycle is already defined.
            return;
        if(solver.walkMode && solver.nVars() < maxVariablesForWalker)
            createSequence("BW BO BI BW BR BF");
        else
            createSequence("BO BI BR BF");
    }


    inline void createSequence(std::string sequence) {
        cycle.clear();
        for(auto c : sequence) {
            if(c == ' ') continue; // separator
            if(c == 'B') cycle.push(best);
            if(c == 'F') cycle.push(flipped);
            if(c == 'O') cycle.push(original);
            if(c == 'I') cycle.push(inverted);
            if(c == 'R') cycle.push(random);
            if(c == 'W') cycle.push(walk);
        }
    }


    inline bool rephasing() const { return nextRephasing < solver.conflicts; }


    inline void updateBestPhase() {
        unsigned int sz = solver.trail_lim.size() >= 1 ? solver.trail_lim[solver.trail_lim.size() - 1] : 0;
        if(sz < minSize && sz > 0) minSize = sz;
        if(sizeBestPhase < sz) {
            int nbV = solver.nVars();
            for(int v = 0; v < nbV; v++) bestPolarity[v] = -10;
            for(unsigned int i = 0; i < sz; i++) bestPolarity[var(solver.trail[i])] = sign(solver.trail[i]);
            sizeBestPhase = sz;
            if(sizeBestofthePhase < sizeBestPhase) sizeBestofthePhase = sizeBestPhase;
        }
    }


    inline void reset() {
        // Want to start with best phase
        if(cycle[nbRephasing % cycle.size()] != best) nbRephasing--;
        sizeBestPhase = 0;
    }


    inline lbool rephase() {
        vec<char> &targetPolarity = solver.targetPolarity;
        phase      phase          = cycle[nbRephasing % cycle.size()];
        int        nbV            = solver.nVars();
        switch(phase) {
            case best: {
                solver.verbose.log(DEBUGVERBOSE, "B (size = %u  -- %u%%) (best of the best = %u %u%%)\n", sizeBestPhase,
                                   sizeBestPhase * 100 / nbV, sizeBestofthePhase, sizeBestofthePhase * 100 / nbV);

                for(int i = 0; i < nbV; i++) targetPolarity[i] = bestPolarity[i];
                solver.phasesUsedDuringSearch += "B";
                break;
            }
            case flipped:
                solver.verbose.log(DEBUGVERBOSE, "F\n");
                for(int i = 0; i < nbV; i++) targetPolarity[i] = ~targetPolarity[i];
                solver.phasesUsedDuringSearch += "F";
                break;
            case original:
                solver.verbose.log(DEBUGVERBOSE, "O\n");
                for(int i = 0; i < nbV; i++) targetPolarity[i] = false;
                solver.phasesUsedDuringSearch += "O";
                break;
            case inverted:
                solver.verbose.log(DEBUGVERBOSE, "I\n");
                for(int i = 0; i < nbV; i++) targetPolarity[i] = true;
                solver.phasesUsedDuringSearch += "I";
                break;
            case random: {   // As in glucose3 rephase (see pragmatics of sat
                solver.verbose.log(DEBUGVERBOSE, "R\n");
                solver.phasesUsedDuringSearch += "R";
                for(int i = 0; i < targetPolarity.size(); ++i) targetPolarity[i] = solver.random.nextDouble() < 0.5;
                break;
            }
            case walk:
                solver.phasesUsedDuringSearch += "W";
                solver.cancelUntil(0);   // Reboot solver
                if(ccanr.solve() != l_Undef) return l_True;
                break;
        }
        nbRephasing++;
        nextRephasing = solver.conflicts + nbRephasing * 1000;
        sizeBestPhase = 0;
        return l_Undef;
    }
};
}   // namespace Glucose


#endif   // GLUCOSE_TARGETPHASE_H
