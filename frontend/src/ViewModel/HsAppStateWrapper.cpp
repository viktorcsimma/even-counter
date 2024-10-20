#include "ViewModel/HsAppStateWrapper.hpp"
#include "ViewModel/OddParameterException.hpp"
#include "Acorn.h"

HsAppStateWrapper::HsAppStateWrapper():
    // an std::thread with an empty constructor does not really represent a thread
    appStatePtr(initAppInt()), evaluationThread(), evaluating(false) {}

int HsAppStateWrapper::getCounterValue() const {
    return getCounterValueInt(appStatePtr);
}

void HsAppStateWrapper::incrementWith(int toAdd) {
    if (0 != incrementWithInt(appStatePtr, toAdd)) {
        throw OddParameterException();
    } // else, we are fine
}

int HsAppStateWrapper::increaseFor(int duration) {
    return increaseContinuouslyInt(appStatePtr, duration);
}

bool HsAppStateWrapper::interruptEvaluation() {
    if (evaluating) {
        // this is defined in Acorn.h
        acornInterruptEvaluation();
        // let's join it; that is safer
        // hopefully, it ends quickly
        evaluationThread.join();

        evaluating = false;
        return true;
    } else return false;
}

HsAppStateWrapper::~HsAppStateWrapper() {
    if (evaluating) interruptEvaluation();
    else if (evaluationThread.joinable()) evaluationThread.detach(); // we have to join or detach it before destruction

    // there is no guarantee that a StablePtr is anything meaningful,
    // so we have to free it from Haskell
    destructAppInt(appStatePtr);
}
