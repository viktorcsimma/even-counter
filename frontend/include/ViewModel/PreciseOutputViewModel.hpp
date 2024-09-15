#ifndef PRECISE_OUTPUT_VIEW_MODEL_HPP_
#define PRECISE_OUTPUT_VIEW_MODEL_HPP_

#include "ViewModel/HsCalcStateWrapper.hpp"

#include <string>

// Represents the members
// the precise output window needs.
// Contains a HsCalcStateWrapper pointer
// which, however, does _not_ get freed on destruction
// (that remains the responsibility of the main view model).
class PreciseOutputViewModel {
    private:
        HsCalcStateWrapper* const calcStateWrapper;
        int precision;
        std::string result;

        // Cuts the type information from the end of the result string.
        void trimTypeNameFromResult();

    public:
        // Gets a pointer to an already-initialised HsCalcStateWrapper
        // which does _not_ get freed on destruction.
        // It also gets the initial result string
        // so that it need not be reevaluated immediately.
        PreciseOutputViewModel(HsCalcStateWrapper* calcStateWrapper,
                               int initialPrecision,
                               std::string initialResult);
        // Sets a new precision and reevaluates the output with it.
        void setPrecision(int precision);
        // Sets a new precision and reevaluates the output with it asynchronously,
        // executing the function given when it's done.
        template<class F>
        void setPrecisionAsync(int precision, F onFinished) {
            calcStateWrapper->reevalCommandAsync(precision, [=](std::string result) {
                this->result = result;
                trimTypeNameFromResult();
                this->precision = precision;
                onFinished();
            });
        }
        // Interrupts the evaluation and returns true if there is one;
        // returns false otherwise.
        // It joins the thread after the signal is sent
        // until it shuts down gracefully.
        bool interruptEvaluation() {return calcStateWrapper->interruptEvaluation();}
        // Gets the precision currently set.
        int getPrecision() const;
        // A getter for a reference to the result string to be displayed.
        const std::string& getResult() const;
};

#endif
