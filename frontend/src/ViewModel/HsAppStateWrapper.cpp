#include "ViewModel/HsAppStateWrapper.hpp"
#include "Acorn.h"

HsAppStateWrapper::HsAppStateWrapper(): appStatePtr(initAppInteger()) {}

// Of course, this is not too efficient,
// but now we are simulating an environment
// where the backend is fully in the Haskell runtime.
int HsAppStateWrapper::getCounterValue() const {return getCounterValueInteger(appStatePtr);}

bool HsAppStateWrapper::incrementWith(int toAdd) {
    return 0 == incrementInteger(appStatePtr, toAdd);
}

HsAppStateWrapper::~HsAppStateWrapper() {
    hs_free_stable_ptr(appStatePtr);
}
