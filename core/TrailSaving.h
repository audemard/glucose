//
// Created by audemard on 21/10/2020.
//

#ifndef GLUCOSE_TRAILSAVING_H
#define GLUCOSE_TRAILSAVING_H

#include "Solver.h"
//#include "core/SolverTypes.h"

namespace Glucose {
class Solver;

class TrailSaving {
   public:
    bool active;

   protected:
    Solver &  solver;
    vec<Lit>  oldTrail, &trail;
    vec<CRef> oldReasons;
    int       oldTrailQhead;

   public:
    TrailSaving(Solver &solver1, bool a) : active(a), solver(solver1), trail(solver.trail), oldTrailQhead(0) { }


    void initialize() {
        oldTrail.growTo(solver.nVars());
        oldReasons.growTo(solver.nVars());
    }


    void activate(bool b) { active = b; }


    void reset() {
        for(auto &i : oldTrail) oldReasons[var(i)] = CRef_Undef;

        oldTrail.clear();
        oldTrailQhead = 0;
    }


    bool onBacktrack(int level) {
        if(active == false) return false;
        reset();
        bool savetrail = (solver.decisionLevel() - level > 1);
        if(savetrail)
            for(int i = trail.size() - 1; i >= solver.trail_lim[level]; i--) oldTrail.push_(lit_Undef);
        return savetrail;
    }


    void onCancel(int c, int level) {
        if(active == false) return;
        oldTrail[c - solver.trail_lim[level]] = trail[c];
        oldReasons[var(trail[c])]             = solver.reason(var(trail[c]));
    }


    CRef useSaveTrail(Lit p) {
        if(active == false) return CRef_Undef;
        Lit  old_trail_top = lit_Undef;
        CRef old_reason    = CRef_Undef;

        if(oldTrailQhead < oldTrail.size()) {
            old_trail_top = oldTrail[oldTrailQhead];
            old_reason    = oldReasons[var(old_trail_top)];
        }

        if(p == old_trail_top) {
            while(oldTrailQhead < oldTrail.size() - 1) {
                oldTrailQhead++;
                old_trail_top = oldTrail[oldTrailQhead];
                old_reason    = oldReasons[var(old_trail_top)];
                if(old_reason == CRef_Undef)
                    break;
                else if(solver.value(old_trail_top) == l_False)
                    return old_reason;
                else if(solver.value(old_trail_top) == l_Undef)
                    solver.uncheckedEnqueue(old_trail_top, old_reason);
            }
        } else if(var(p) == var(old_trail_top))
            reset();
        else if(solver.value(old_trail_top) == l_False)
            reset();

        return CRef_Undef;
    }


    void reloc(ClauseAllocator &to) {
        for(int i = 0; i < oldTrail.size(); i++) {
            Var v = var(oldTrail[i]);

            if(oldReasons[v] != CRef_Undef && (solver.ca[oldReasons[v]].reloced())) solver.ca.reloc(oldReasons[v], to);
        }
    }
};
}   // namespace Glucose

#endif   // GLUCOSE_TRAILSAVING_H
