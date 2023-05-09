//
// Created by audemard on 30/11/2020.
//

#ifndef GLUCOSE_RANDOM_H
#define GLUCOSE_RANDOM_H
#include <stdint.h>
namespace Glucose {

struct xorshift128_state {
    uint32_t a, b, c, d;
};


class Random {
    struct xorshift128_state state;
    /* The state array must be initialized to not be all zero */
    uint32_t xorshift128() {
        /* Algorithm "xor128" from p. 5 of Marsaglia, "Xorshift RNGs" */
        uint32_t t = state.d;

        uint32_t const s = state.a;
        state.d          = state.c;
        state.c          = state.b;
        state.b          = s;

        t ^= t << 11;
        t ^= t >> 8;
        return state.a = t ^ s ^ (s >> 19);
    }

   public:
    Random(uint32_t _s) { setSeed(_s); }

    void setSeed(uint32_t _s) {
        state.a = _s & 123479117;
        state.b = _s | 123479117;
        state.c = _s & 62346811819;
        state.d = _s | 62346811819;
    }

    uint32_t nextInt() { return xorshift128(); }

    uint32_t nextInt(int max) { return xorshift128() % max; }

    double nextDouble() { return (double)xorshift128() * (1. / (65536. * 65536.)); }   // Return a double in [0,1)
};

}   // namespace Glucose

#endif   // GLUCOSE_RANDOM_H
