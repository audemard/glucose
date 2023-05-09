#include "Restart.h"

#include <iostream>

#include "Solver.h"

using namespace Glucose;


void GlucoseRestart::update(unsigned int trail, unsigned int lbd) {
    ema_trail_wide.update(trail);
    lastTrailSize = trail;
    ema_lbd_narrow.update(lbd);
    ema_lbd_wide.update(lbd);
}


bool GlucoseRestart::blockRestart() {
    if(lastTrailSize > block * ema_trail_wide && solver.conflicts >= minimumConflictsForBlockingRestarts) {
        minimum_conflicts = solver.conflicts + 50;
        nbBlocked++;
        return true;
    }
    return false;
}


bool GlucoseRestart::triggerRestart() {
    if(solver.conflicts < minimum_conflicts) return false;

    if(ema_lbd_narrow / ema_lbd_wide > force) {
        nbRestarts++;
        minimum_conflicts = solver.conflicts + 50;
        return true;
    }
    return false;
}


GlucoseRestart::GlucoseRestart(Solver& _solver)
    : Restart(_solver), minimum_conflicts(50), minimumConflictsForBlockingRestarts(10000), ema_lbd_narrow(3e-2),
      ema_lbd_wide(1e-5), ema_trail_wide(3e-4), lastTrailSize(0), force(1.25), block(1.4), nbRestarts(0), nbBlocked(0) { }


/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */


static uint64_t luby(double y, unsigned int x) {
    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    unsigned int size, seq;
    for(size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1)
        ;

    while(size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }
    return pow(y, seq);
}


bool LubyRestart::triggerRestart() {
    if(solver.conflicts <= limit) return false;
    limit = solver.conflicts + luby(2, curr_restarts) * step;
    curr_restarts++;
    nbRrestarts++;
    return true;
}