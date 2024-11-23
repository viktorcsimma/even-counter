#include "ViewModel/Future.hpp"
#include "Future.h" // the Haskell stub

template<>
int Future<int>::haskellGet() {
    return getCIntFromFutureC(stablePtrs);
}
