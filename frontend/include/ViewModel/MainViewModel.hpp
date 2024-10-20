#ifndef MAIN_VIEW_MODEL_HPP_
#define MAIN_VIEW_MODEL_HPP_

#include <string>

#include "HsAppStateWrapper.hpp"

// A view model containing different elements
// which the main window will need.
class MainViewModel {
    private:
        // This will be a pointer;
        // it needs to be swappable
        // and that is easier to do this way.
        HsAppStateWrapper* appStateWrapper;
        std::string displayedText;

    public:
        // This also automatically constructs a HsAppStateWrapper
        // and stores its pointer.
        MainViewModel(): appStateWrapper(new HsAppStateWrapper()), displayedText(std::to_string(appStateWrapper->getCounterValue())) {}

        // Executes an "add" command with the given number as a parameter.
        // Throws an OddParameterException if the parameter given is odd.
        void incrementWith(int toAdd) {
            appStateWrapper->incrementWith(toAdd);
            this->displayedText = std::to_string(this->appStateWrapper->getCounterValue());
        }

        // Whether there is an asynchronous calculation running.
        bool isEvaluating() const {return appStateWrapper->isEvaluating();}

        // Begins a continuous increasing of the counter
        // by two every second;
        // for the given period (in seconds)
        // or until interrupted.
        // Executes onFinished if finished orderly
        // or onInterrupted if interrupted.
        template<class F, class G>
        void increaseForAsync(int period, F onFinished, G onInterrupted) {
            appStateWrapper->increaseForAsync(period, [=](int result) {
                this->displayedText = std::to_string(this->appStateWrapper->getCounterValue());
                if (0 == result) {
                    onFinished();
                } else {
                    this->displayedText += " (interrupted)";
                    onInterrupted();
                }
            });
        }

        // Interrupts the current asynchronous computation, joins it until it stops gracefully
        // and returns true if there was one;
        // returns false otherwise.
        bool interruptEvaluation() {return appStateWrapper->interruptEvaluation();}

        // This also frees the HsAppStateWrapper.
        ~MainViewModel() {delete appStateWrapper;}

        // Getters returning constant references.
        const std::string& getDisplayedText() const {return displayedText;}

        // We delete the copy constructor and the assignment operator.
        MainViewModel(const MainViewModel& temp_obj) = delete; 
        MainViewModel& operator=(const MainViewModel& temp_obj) = delete;
};

#endif
