#ifndef HS_CALC_STATE_WRAPPER_HPP_
#define HS_CALC_STATE_WRAPPER_HPP_

#include <string>
#include <thread>

#include "TinyHsFFI.h"

#include "ViewModel/RealBaseType.hpp"

class HsCalcStateWrapper {
    private:
    static const RealBaseType DEFAULT_BASE_TYPE = DyadicBase;

    // Indicates whether the Haskell r

    // A pointer to the Haskell CalcState object;
    // this is what will be passed to Haskell functions.
    const HsStablePtr calcStatePtr;
    // The underlying type of reals
    // (e.g. Dyadic if the object is a CalcState (C Dyadic)).
    // For now, this can't be changed;
    // the only way is to create a new CalcState object,
    // with all variables lost.
    // (But there wouldn't be much demand, anyway.)
    const RealBaseType baseType;
    // The thread running the actual reevalCommand
    // (if isEvaluating is false, it has either terminated or is invalid;
    // see joinable()).
    std::thread evaluationThread;
    // Whether there is an asynchronous evaluation in progress.
    bool isEvaluating;

    public:
    // The constructor.
    // This also creates the Haskell object and fetches its pointer.
    // Beware: it assumes that the runtime has already been initalised.
    HsCalcStateWrapper(RealBaseType baseType = DEFAULT_BASE_TYPE);
    // Executes a command and returns a string as a result,
    // in the format "0.12345 :: Rational".
    // Might return an error (starting with "error:").
    // The precision is given in the number of digits after the decimal point.
    std::string execCommand(const char* command, int precision) const;
    // Recalculates the last result with another precision.
    // Note that this does _not_ have the side effects tthere possible were.
    std::string reevalCommand(int precision) const;
    // Runs reevalCommand() asynchronously, on a new thread
    // and executes the given function with the result string as the parameter on the same thread
    // after this is done.
    template<class StringFunction>
    void reevalCommandAsync(int precision, StringFunction onFinish) {
        // destructing a thread is not safe if it is joinable;
        // even if it has terminated
        if (evaluationThread.joinable()) evaluationThread.join();
        isEvaluating = true;
        evaluationThread = std::thread([=]() {
            std::string result = reevalCommand(precision);
            onFinish(result);
            isEvaluating = false;
        });
    }
    // Interrupts the current computation, joins it until it stops gracefully
    // and returns true if there was one;
    // returns false otherwise.
    bool interruptEvaluation();

    // The destructor.
    // This also runs interruptEvaluation() and frees the StablePtr
    // but does not shut down the runtime.
    ~HsCalcStateWrapper();

    // We delete the copy constructor and the assignment operator.
    HsCalcStateWrapper(const HsCalcStateWrapper& temp_obj) = delete; 
    HsCalcStateWrapper& operator=(const HsCalcStateWrapper& temp_obj) = delete; 
};

#endif
