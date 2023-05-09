#ifndef VERBOSE_H
#define VERBOSE_H

#include <stdarg.h>
#include <stdio.h>

#define NOVERBOSE    -1
#define NORMAL       1
#define DEBUGVERBOSE 2
#define FULLVERBOSE  3
#define TOTALVERBOSE 4


// Terminal color
#define KNRM "\x1B[0m"
#define KRED "\x1B[31m"
#define KGRN "\x1B[32m"
#define KYEL "\x1B[33m"
#define KBLU "\x1B[34m"
#define KMAG "\x1B[35m"
#define KCYN "\x1B[36m"
#define KWHT "\x1B[37m"


namespace Glucose {
class Verbose {
   public:
    int verbosity;
    explicit Verbose(int v = NORMAL) : verbosity(v) { }

    void log(int vb, const char* format, ...) const {
        if(vb > verbosity) return;
        va_list argptr;
        va_start(argptr, format);
        vfprintf(stdout, format, argptr);
        va_end(argptr);
    }
};
};   // namespace Glucose

#endif /* VERBOSE_H */
