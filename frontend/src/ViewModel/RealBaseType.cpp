#include "ViewModel/RealBaseType.hpp"

#include <cstring>

RealBaseType stringToRealBaseType(const char* name) {
    if (strcmp("Dyadic", name) == 0 || strcmp("DyadicBase", name)) return DyadicBase;
    else if (strcmp("Rational", name) == 0 || strcmp("RationalBase", name) == 0) return RationalBase;
    else throw "Unknown RealBaseType";
}