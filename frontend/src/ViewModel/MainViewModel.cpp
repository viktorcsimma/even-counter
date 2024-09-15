#include "ViewModel/MainViewModel.hpp"

#include <cstring>

MainViewModel::MainViewModel(RealBaseType realBaseType, int precision):
    calcStateWrapper(new HsCalcStateWrapper(realBaseType)),
    primaryText("0"), secondaryText(""), realBaseType(realBaseType),
    precision(precision) {}

// Separates the result itself from the type
// in case of a valid result.
const char* RESULT_TYPE_SEPARATOR = " :: ";
const int RESULT_TYPE_SEPARATOR_LENGTH = strlen(RESULT_TYPE_SEPARATOR);
// If this is at the beginnning of the result string,
// that indicates there has been an error.
const char* ERROR_MARKER = "error";

void MainViewModel::enterCommand(const char* command) {
    std::string result = calcStateWrapper->execCommand(command, precision);
    if (0 == result.rfind(ERROR_MARKER, 0)) {
        // the primary text remains the same
        secondaryText = result;
    } else {
        // cut it up on " :: "
        int cutIndex = result.find(RESULT_TYPE_SEPARATOR);
        // break into two substrings
        primaryText = result.substr(0, cutIndex);
        secondaryText = result.substr(cutIndex + RESULT_TYPE_SEPARATOR_LENGTH);
    }
}

void MainViewModel::switchMode(RealBaseType realBaseType) {
    // if we are already in that mode, we do nothing
    if (this->realBaseType != realBaseType) {
        // otherwise, we throw away everything
        delete calcStateWrapper;
        calcStateWrapper = new HsCalcStateWrapper(realBaseType);
        primaryText = "0";
        secondaryText = "";
        this->realBaseType = realBaseType;
    }
}

PreciseOutputViewModel MainViewModel::spawnPreciseOutputViewModel() const {
    return PreciseOutputViewModel(calcStateWrapper, precision, primaryText);
}

void MainViewModel::setPrecision(int precision) {
    this->precision = precision;
}

MainViewModel::~MainViewModel() {
    delete calcStateWrapper;
}

const std::string& MainViewModel::getPrimaryText() const {
    return primaryText;
}

const std::string& MainViewModel::getSecondaryText() const {
    return secondaryText;
}
