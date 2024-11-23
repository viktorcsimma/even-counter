#ifndef HS_APP_STATE_WRAPPER_HPP_
#define HS_APP_STATE_WRAPPER_HPP_

#include "TinyHsFFI.h"
#include "ViewModel/Future.hpp"
#include "Acorn.h"

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

  public:

    // The constructor.
    // This also creates the Haskell object and fetches its pointer.
    // Beware: it assumes that the runtime has already been initalised.
    HsAppStateWrapper();

    // A getter for the counter value.
    int getCounterValue() const;

    // Adds an even number to the value of the counter.
    // Returns false if the operation has not been successful
    // (i.e. toAdd was odd -- but we let the backend determine this).
    bool incrementWith(int toAdd);

    // On a new thread, this begins to continuously increase the value of the counter
    // by 2 every second,
    // for the duration given in seconds or until interrupted.
    // Returns a Future through which we can wait for the result,
    // which is the final state of the counter.
    // Interruption is possible via the Future object returned.
    Future<int> increaseContinuouslyAsync(int duration) {
      return Future<int>([this, duration](HsPtr futurePtr){increaseContinuouslyIntegerAsyncC(appStatePtr, duration, futurePtr);});
    }

    // The destructor.
    // This also runs interruptEvaluation() and frees the StablePtr
    // but does not shut down the runtime.
    ~HsAppStateWrapper();

    // We delete the copy constructor and the assignment operator.
    HsAppStateWrapper(const HsAppStateWrapper& temp_obj) = delete; 
    HsAppStateWrapper& operator=(const HsAppStateWrapper& temp_obj) = delete; 
};

#endif
