#include "ViewModel/MainViewModel.hpp"
#include "ViewModel/AsyncCalculationAlreadyInProgressException.hpp"

MainViewModel::MainViewModel():
    appStateWrapper(new HsAppStateWrapper()), displayedText(std::to_string(appStateWrapper->getCounterValue())),
    actualFuture(nullptr), _hasError(false) {}

void MainViewModel::incrementWith(int toAdd) {
    std::unique_lock lock(mutex);
    _hasError = !(appStateWrapper->incrementWith(toAdd));
    displayedText = std::to_string(appStateWrapper->getCounterValue());
}

void MainViewModel::incrementAsync() {
    _hasError = false;
    std::unique_lock lock(mutex);
    if (nullptr != actualFuture) throw AsyncCalculationAlreadyInProgressException();
    actualFuture = new Future<int>(appStateWrapper->increaseContinuouslyAsync(1));
}

void MainViewModel::incrementManyTimesAsync(int duration, std::vector<std::function<void(int)>> triggersOnIteration,
                                                          std::vector<std::function<void(int)>> triggersOnFinish) {
    if (nullptr != actualFuture) throw AsyncCalculationAlreadyInProgressException();
    triggerThread = std::thread([triggersOnIteration, triggersOnFinish, duration, this]() {
        try {
            for (int i=0; i<duration; ++i) {
                incrementAsync();
                int result = actualFuture->get();
                std::unique_lock lock(mutex);
                displayedText = std::to_string(result);
                for (const std::function<void(int)> &t: triggersOnIteration) t(result);
                if (duration-1 == i) {
                    for (const std::function<void(int)> &t: triggersOnFinish) t(result);
                }
                // we have to avoid double deletes
                if (nullptr != actualFuture) {
                    delete actualFuture;
                    actualFuture = nullptr;
                }
            }
        } catch(InterruptedFutureException) {} // if interrupted
    });
}

bool MainViewModel::interrupt() {
    if (nullptr == actualFuture) return false;
    else {
        std::unique_lock lock(mutex);
        actualFuture->interrupt();
        // wait until the thread stops gracefully
        if (triggerThread.joinable()) triggerThread.join();
        // we have to avoid double deletes
        if (nullptr != actualFuture) {
            delete actualFuture;
            actualFuture = nullptr;
        }
        return true;
    }
}

MainViewModel::~MainViewModel() {
    interrupt();
    delete appStateWrapper;
}


