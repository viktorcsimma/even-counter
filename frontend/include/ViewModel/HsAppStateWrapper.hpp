#ifndef HS_APP_STATE_WRAPPER_HPP_
#define HS_APP_STATE_WRAPPER_HPP_

#include <string>
#include <thread>

#include "TinyHsFFI.h"

/**
 * A wrapper class containing
 * a pointer to a Haskell AppState object
 * and handling it in a RAII way.
 */
class HsAppStateWrapper {
  private:

    // A pointer to the Haskell AppState object;
    // this is what will be passed to Haskell functions.
    const HsStablePtr appStatePtr;
    // The thread running the actual interruptible call
    // (if isEvaluating is false, it has either terminated or is invalid;
    // see joinable()).
    std::thread evaluationThread;
    // Whether there is an asynchronous evaluation in progress.
    bool evaluating;

  public:
    // The constructor.
    // This also creates the Haskell object and fetches its pointer.
    // Beware: it assumes that the runtime has already been initalised.
    HsAppStateWrapper();

    // A getter for the counter value.
    int getCounterValue() const;

    // Whether there is an asynchronous calculation running.
    bool isEvaluating() const {return evaluating;}

    // Adds an even number to the value of the counter.
    // Throws an OddParameterException if the parameter given is odd.
    void incrementWith(int toAdd);

  private:
    // Begins to continuously increase the value of the counter
    // by 2 every second,
    // for the duration given in seconds or until interrupted.
    // Returns -1 if interrupted
    // or 0 otherwise.
    // Its result should be used by the handler function
    // passed to increaseForAsync.
    int increaseFor(int duration);

  public:
    // On a new thread, this begins to continuously increase the value of the counter
    // by 2 every second,
    // for the duration given in seconds or until interrupted.
    // It cannot run triggers on an individual value change;
    // that could be solved e.g. by the Haskell backend sending signals back.
    template<class Function>
    void increaseForAsync(int duration, Function onFinish) {
        // destructing a thread is not safe if it is joinable;
        // even if it has terminated
        if (evaluationThread.joinable()) evaluationThread.join();
        evaluating = true;
        evaluationThread = std::thread([=]() {
            onFinish(increaseFor(duration));
            evaluating = false;
        });
    }
    // Interrupts the current computation, joins it until it stops gracefully
    // and returns true if there was one;
    // returns false otherwise.
    bool interruptEvaluation();

    // The destructor.
    // This also runs interruptEvaluation() and frees the StablePtr
    // but does not shut down the runtime.
    ~HsAppStateWrapper();

    // We delete the copy constructor and the assignment operator.
    HsAppStateWrapper(const HsAppStateWrapper& temp_obj) = delete; 
    HsAppStateWrapper& operator=(const HsAppStateWrapper& temp_obj) = delete; 
};

#endif
