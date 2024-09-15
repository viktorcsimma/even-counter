#include "ViewModel/HsCalcStateWrapper.hpp"
#include "Acorn.h"

// This creates the CalcState object
// and returns the HsStablePtr.
// It is only a separate function
// because we need it for initialisation;
// it should _not_ be used elsewhere.
static HsStablePtr initStablePtr(RealBaseType baseType) {
    return (DyadicBase == baseType)
         ? initCalcDyadic()
         : initCalcRational();
}

HsCalcStateWrapper::HsCalcStateWrapper(RealBaseType baseType):
    // an std::thread with an empty constructor does not really represent a thread
    calcStatePtr(initStablePtr(baseType)), baseType(baseType), evaluationThread(), isEvaluating(false) {}

std::string
  HsCalcStateWrapper::execCommand(const char* command, int precision) const {
    const char* result
      = (DyadicBase == baseType)
      ? (char*) execCommandDyadic(calcStatePtr, (char*) command, precision)
      : (char*) execCommandRational(calcStatePtr, (char*) command, precision);
    // we copy it into a string
    std::string toReturn(result);
    // in theory, this can be freed from here
    free((void *) result);
    // and we hope this gets a return-value optimisation
    return toReturn;
}

std::string HsCalcStateWrapper::reevalCommand(int precision) const {
    // similarly
    const char* result
      = (DyadicBase == baseType)
      ? (char*) reevalCommandDyadic(calcStatePtr, precision)
      : (char*) reevalCommandDyadic(calcStatePtr, precision);
    // we copy it into a string
    std::string toReturn(result);
    // in theory, this can be freed from here
    free((void *) result);
    // and we hope this gets a return-value optimisation
    return toReturn;
}

bool HsCalcStateWrapper::interruptEvaluation() {
    if (isEvaluating) {
        // this is defined in Acorn.h
        acornInterruptEvaluation();
        // let's join it; that is safer
        // hopefully, it ends quickly
        evaluationThread.join();

        isEvaluating = false;
        return true;
    } else return false;
}

HsCalcStateWrapper::~HsCalcStateWrapper() {
    if (isEvaluating) interruptEvaluation();
    else if (evaluationThread.joinable()) evaluationThread.detach(); // we have to join or detach it before destruction

    // there is no guarantee that a StablePtr is anything meaningful,
    // so we have to free it from Haskell
    if (DyadicBase == baseType) destructCalcDyadic(calcStatePtr);
    else destructCalcRational(calcStatePtr);
}
