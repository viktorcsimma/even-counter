#ifndef MAIN_VIEW_MODEL_HPP_
#define MAIN_VIEW_MODEL_HPP_

#include <string>

#include "HsCalcStateWrapper.hpp"
#include "PreciseOutputViewModel.hpp"

// A view model containing different elements
// which the main window will need.
class MainViewModel {
    private:
        // This will be a pointer;
        // it needs to be swappable
        // and that is easier to do this way.
        HsCalcStateWrapper* calcStateWrapper;
        std::string primaryText;
        std::string secondaryText;
        RealBaseType realBaseType;
        // The default precision of results.
        int precision;

    public:
        // This automatically constructs a HsCalcStateWrapper
        // with the given base type.
        MainViewModel(RealBaseType realBaseType, int precision);
        // Executes a command and changes the state of the members
        // according to it.
        void enterCommand(const char* command);
        // Switches the base type.
        // For now, this deletes everything in the history
        // and creates a new calcStateWrapper
        // while freeing the previous one.
        void switchMode(RealBaseType realBaseType);
        // Spawns a PreciseOutputViewModel
        // bound to the same HsCalcStateWrapper,
        // with the same precision
        // (as we need not reevaluate immediately this way).
        PreciseOutputViewModel spawnPreciseOutputViewModel() const;
        // Sets a new precision for future results
        // (this does _not_ recalculate history items,
        //  nor the current result).
        void setPrecision(int precision);
        // This also frees the HsCalcStateWrapper.
        ~MainViewModel();

        // Getters returning constant references.
        const std::string& getPrimaryText() const;
        const std::string& getSecondaryText() const;        
};

#endif
