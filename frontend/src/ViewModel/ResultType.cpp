#include "ViewModel/ResultType.hpp"

#include <cstring>

ResultType stringToResultType(const char* name) {
    if (strcmp("Bool", name) == 0) return Bool;
    else if (strcmp("Integer", name) == 0) return Integer;
    else if (strcmp("Rational", name) == 0) return Rational;
    else if (strcmp("Real", name) == 0) return Real;
    else throw "Unknown ResultType";
}