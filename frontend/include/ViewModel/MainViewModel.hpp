#ifndef MAIN_VIEW_MODEL_HPP_
#define MAIN_VIEW_MODEL_HPP_

#include <string>
#include <mutex>
#include <thread>

#include "Backend/Future.hpp"
#include "Backend/HsAppStateWrapper.hpp"

// A view model containing different elements
// which the main window will need.
class MainViewModel {
    private:
        // This will be a containment;
        // it only has the size of a pointer
        // and no swapping is needed
        // in the lifetime of the view model.
        HsAppStateWrapper appStateWrapper;

        std::string displayedText;

        // Points to the actual interruptible calculation, if any.
        Future<int>* actualFuture;

        // A mutex embedded in the object.
        std::mutex mutex;

        // The thread on which we will run the get() calls and the triggers.
        std::thread triggerThread;

        // Whether there has been an error we want to sign to the view
        // (i.e. because the value with which to increment the counter has been odd).
        bool _hasError;

    public:
        // This also automatically constructs a HsAppStateWrapper
        // and stores its pointer.
        MainViewModel();

        // Executes an "add" command with the given number as a parameter.
        // Sets hasError if the parameter given is odd.
        void incrementWith(int toAdd);

        // Whether there is an asynchronous calculation running.
        bool isEvaluating() const {return nullptr != actualFuture;}

        // Whether there has been an error we want to sign to the view
        // (i.e. because the value with which to increment the counter has been odd).
        bool hasError() const {return _hasError;}

        // Increases the counter asynchronously:
        // waits for a single second,
        // then makes an increment of two.
        // Does so via the Future construct
        // to demonstrate its capabilities.
        // **Note:** throws if called while an asynchronous calculation is already in progress.
        // Returns immediately with the Future created,
        // which will contain the final state of the counter.
        void incrementAsync();

        // Starts a calculation in which
        // the counter is incremented by 2 every second,
        // until interrupted or for the duration given.
        // Sets hasError to false.
        // triggersOnIteration run on the conclusion of each iteration;
        // triggersOnFinish run only on the conclusion of the final one.
        void incrementManyTimesAsync(int duration, std::vector<std::function<void(int)>> triggersOnIteration = std::vector<std::function<void(int)>>(0),
                                                   std::vector<std::function<void(int)>> triggersOnFinish = std::vector<std::function<void(int)>>(0));

        // Interrupts the asynchronous calculation, if any.
        // Returns false if there has not been any.
        bool interrupt();

        // This also frees the HsAppStateWrapper.
        ~MainViewModel();

        // Getters returning constant references.
        const std::string& getDisplayedText() const {return displayedText;}

        // We delete the copy constructor and the assignment operator.
        MainViewModel(const MainViewModel& temp_obj) = delete;
        MainViewModel& operator=(const MainViewModel& temp_obj) = delete;
};

#endif
