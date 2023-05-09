/*************************************************************************************************
Candy -- Copyright (c) 2015-2019, Markus Iser, KIT - Karlsruhe Institute of Technology

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

#ifndef SRC_CANDY_CORE_RESTART_H_
#define SRC_CANDY_CORE_RESTART_H_

#include <cstdint>

#include "Solver.h"


namespace Glucose {
class Solver;


// Exponential Moving Average (EMA)
// Implementation of the "robust initialization" like in Cadical by Armin Biere
class EMA {
    double       value;
    float        alpha, beta;
    unsigned int wait, period;

   public:
    EMA(double alpha_) : value(1), alpha(alpha_), beta(1), wait(1), period(1) { }


    void update(double next) {
        value += beta * (next - value);

        if(beta > alpha && --wait == 0) {
            wait = period = (2 * period);
            beta *= .5;
            if(beta < alpha) beta = alpha;
        }
    }


    operator double() const { return value; }
};


class Restart {
   protected:
    Solver &solver;

   public:
    explicit Restart(Solver &_solver) : solver(_solver) { }


    virtual bool triggerRestart() = 0;


    virtual bool blockRestart() { return true; };
};


class GlucoseRestart : public Restart {
    uint64_t      minimum_conflicts;
    unsigned long minimumConflictsForBlockingRestarts;
    EMA           ema_lbd_narrow;
    EMA           ema_lbd_wide;
    EMA           ema_trail_wide;
    unsigned int  lastTrailSize;
    float         force;   // 1.25
    float         block;   // 1.4

   public:
    unsigned int nbRestarts, nbBlocked;


    explicit GlucoseRestart(Solver &_solver);


    ~GlucoseRestart() = default;


    void update(unsigned int trail, unsigned int lbd);

    bool triggerRestart() override;

    bool blockRestart() override;
};


class LubyRestart : public Restart {
   public:
    unsigned int nbRrestarts;
    unsigned int step, curr_restarts;
    uint64_t     limit;


    LubyRestart(Solver &_solver) : Restart(_solver), nbRrestarts(0), step(100), curr_restarts(0), limit(100) { }


    bool triggerRestart() override;
};
} /* namespace Glucose */

#endif
