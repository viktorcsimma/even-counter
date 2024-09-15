#include "ViewModel/HsCalcStateWrapper.hpp"
#include "ViewModel/MainViewModel.hpp"

#include <catch2/catch_test_macros.hpp>

#include <catch2/reporters/catch_reporter_event_listener.hpp>
#include <catch2/reporters/catch_reporter_registrars.hpp>

// TODO: some test cases for the interruption mechanism

// We will use these quite often.
// See https://stackoverflow.com/questions/4770985/how-to-check-if-a-string-starts-with-another-string-in-c/4770992#4770992.
bool startsWith(const char* haystack, const char* needle) {
    return strncmp(needle, haystack, strlen(needle)) == 0;
}
bool endsWith(const char* haystack, const char* needle) {
    // stepping to the end
    int i = 0, j = 0;
    while ('\0' != haystack[i]) ++i;
    while ('\0' != needle[j]) ++j;
    if (i < j) return false; // that would mean the needle is longer
    else {
        bool toreturn = true;
        while (toreturn && j >= 0) {
            if (haystack[i] != needle[j]) toreturn = false;
            else {--i; --j;}
        }
        return toreturn;
    }
}
// The number of digits after the decimal point.
// Only works reliably if the string really begins with a number.
int digitsAfterDecimalPoint(const char* number) {
    while ('\0' != *number && ' ' != *number && '.' != *number) ++number;
    if ('.' != *number) return 0;
    else {
        ++number;
        int counter = 0;
        while ('0' <= *number && *number <= '9') {++number; ++counter;}
        return counter;
    }
}

TEST_CASE("HsCalcStateWrapper") {
    HsCalcStateWrapper calcStateWrapper(DyadicBase);
    
    SECTION("executing a legal evaluation command") {
        std::string result = calcStateWrapper.execCommand("1 + sqrt(2)", 10);
        REQUIRE(startsWith(result.c_str(), "2.41"));
        REQUIRE(endsWith(result.c_str(), " :: Real"));
    }

    // TODO: check number of significant digits instead of those after the decimal point
    // when we have done that
    SECTION("output is at least as long as precision (for rationals and reals)") {
        std::string result = calcStateWrapper.execCommand("1 + sqrt(2)", 10);
        REQUIRE(digitsAfterDecimalPoint(result.c_str()) >= 10);
        result = calcStateWrapper.reevalCommand(50);
        REQUIRE(digitsAfterDecimalPoint(result.c_str()) >= 50);
    }

    SECTION("checking types") {
        std::string result = calcStateWrapper.execCommand("t = 3 == 5", 10);
        REQUIRE("False :: Bool" == result);
        result = calcStateWrapper.execCommand("t = 5 - 2", 10);
        REQUIRE("3 :: Integer" == result);
        result = calcStateWrapper.execCommand("t = t / 5", 10);
        REQUIRE("0.6 :: Rational" == result);
        result = calcStateWrapper.execCommand("t = sqrt(t)", 10);
        REQUIRE(startsWith(result.c_str(), "0.77"));
        REQUIRE(endsWith(result.c_str(), " :: Real"));
    }

    SECTION("handling whitespace while parsing") {
        std::string result = calcStateWrapper.execCommand("t=3==5", 10);
        REQUIRE("False :: Bool" == result);
        result = calcStateWrapper.execCommand("        t=3 ==5     ", 10);
        REQUIRE("False :: Bool" == result);
        result = calcStateWrapper.execCommand("sqrt      ( 2 )", 10);
        REQUIRE(!startsWith(result.c_str(), "error"));
        result = calcStateWrapper.execCommand("sqrt(2)", 10);
        REQUIRE(!startsWith(result.c_str(), "error"));
        // we can add other test cases, too
    }

    SECTION("executing an illegal evaluation command") {
        std::string result = calcStateWrapper.execCommand("False + True", 10);
        REQUIRE(endsWith(result.c_str(), "operator '+' is not applicable to booleans"));
    }

    SECTION("creating a variable and manipulating it") {
        std::string result = calcStateWrapper.execCommand("t = 5", 10);
        REQUIRE("5 :: Integer" == result);
        result = calcStateWrapper.execCommand("t = 10", 10);
        REQUIRE("10 :: Integer" == result);
        result = calcStateWrapper.execCommand("t = t + 1", 10);
        REQUIRE("11 :: Integer" == result);
        result = calcStateWrapper.execCommand("x = t / 2", 10);
        REQUIRE("5.5 :: Rational" == result);
        result = calcStateWrapper.execCommand("t = sqrt(t - 9) + t", 10);
        REQUIRE("12.4142135624 :: Real" == result); // beware, it should be rounded upwards!
    }

    SECTION("illegal assignment does not have side effects") {
        calcStateWrapper.execCommand("t = 5", 10);
        std::string result = calcStateWrapper.execCommand("t = asdasdasd", 10);
        REQUIRE("error while executing statement; while evaluating value to assign: asdasdasd is undefined"
                            == result);
        result = calcStateWrapper.execCommand("t", 10);
        REQUIRE("5 :: Integer" == result);
    }

    SECTION("reevaluations") {
        std::string result = calcStateWrapper.execCommand("pi", 10);
        SECTION("with same precision") {
            REQUIRE(calcStateWrapper.reevalCommand(10) == result);
        }
        SECTION("with greater precision") {
            result = calcStateWrapper.reevalCommand(50);
            REQUIRE("3.14159265358979323846264338327950288419716939937511 :: Real" // beware, it should be rounded upwards!
                                == result);
        }
        SECTION("with smaller precision") {
            result = calcStateWrapper.reevalCommand(5);
            REQUIRE("3.14159 :: Real" == result);
        }
    }

    SECTION("illegal operations") {
        std::string result = calcStateWrapper.execCommand("pi + True", 10);
        REQUIRE("error while executing statement; while evaluating expression: operator '+' is not applicable to booleans"
                == result);
        result = calcStateWrapper.execCommand("5 / 0", 10);
        REQUIRE("error while executing statement; while evaluating expression: division by integer 0"
                == result);
        result = calcStateWrapper.execCommand("5 / 0.0", 10);
        REQUIRE("error while executing statement; while evaluating expression: division by rational 0"
                == result);
        result = calcStateWrapper.execCommand("history[0]", 10);
        REQUIRE("error while executing statement; while evaluating expression: index 0 is too large"
                == result);

        // real comparisons are not yet added here,
        // as I would like to work on them later
    }

    SECTION("type conversions") {
        std::string result = calcStateWrapper.execCommand("5 + 2 / 3", 10);
        REQUIRE("5.6666666667 :: Rational"
                == result);
        result = calcStateWrapper.execCommand("0.75 + 5", 10);
        REQUIRE("5.75 :: Rational"
                == result);
        result = calcStateWrapper.execCommand("pi + 5", 10);
        REQUIRE("8.1415926536 :: Real"
                == result);
        result = calcStateWrapper.execCommand("0.1 + sqrt(4 / 2)", 10);
        REQUIRE("1.5142135624 :: Real"
                == result);
    }

    /*
    // Some test cases for when we develop control sequences to an official feature.
    SECTION("legal if statements (both true and false)") {}

    SECTION("an illegal if statement has no side effects") {}

    SECTION("legal while statements (also when it is false at the beginning)") {}

    SECTION("an illegal while statement has no side effects") {}

    SECTION("a runtime error in a while statement – what does it do?") {}

    SECTION("value of some expressions") {}
    */
}

TEST_CASE("MainViewModel") {
    MainViewModel mainViewModel(DyadicBase, 10);

    // TODO: check number of significant digits
    // when we have done that
    SECTION("output is at least as long as precision (for rationals and reals)") {
        mainViewModel.enterCommand("1 / 3");
        REQUIRE(digitsAfterDecimalPoint(mainViewModel.getPrimaryText().c_str()) >= 10);
        mainViewModel.enterCommand("sqrt(2)");
        REQUIRE(digitsAfterDecimalPoint(mainViewModel.getPrimaryText().c_str()) >= 10);
    }
    SECTION("setting different precision") {
        mainViewModel.setPrecision(50);

        mainViewModel.enterCommand("1 / 3");
        REQUIRE(digitsAfterDecimalPoint(mainViewModel.getPrimaryText().c_str()) >= 50);
        mainViewModel.enterCommand("sqrt(2)");
        REQUIRE(digitsAfterDecimalPoint(mainViewModel.getPrimaryText().c_str()) >= 50);
    }

    SECTION("displaying result of legal evaluations and assignments") {
        mainViewModel.enterCommand("3 == 5");
        REQUIRE("False" == mainViewModel.getPrimaryText());
        REQUIRE("Bool" == mainViewModel.getSecondaryText());
        mainViewModel.enterCommand("t = 5 - 2");
        REQUIRE("3" == mainViewModel.getPrimaryText());
        REQUIRE("Integer" == mainViewModel.getSecondaryText());
        mainViewModel.enterCommand("t = t / 5");
        REQUIRE("0.6" == mainViewModel.getPrimaryText());
        REQUIRE("Rational" == mainViewModel.getSecondaryText());
        mainViewModel.enterCommand("t = sqrt(t)");
        REQUIRE(startsWith(mainViewModel.getPrimaryText().c_str(), "0.77"));
        REQUIRE("Real" == mainViewModel.getSecondaryText());
    }
    // TODO: other statement types?

    SECTION("displaying error") {
        mainViewModel.enterCommand("3 == 5");
        mainViewModel.enterCommand("3 / 0");
        // the command remains in the primary textbox
        REQUIRE("error while executing statement; while evaluating expression: division by integer 0"
                == mainViewModel.getSecondaryText());
    }

    SECTION("it still works after switching base type") {
        mainViewModel.enterCommand("sqrt(5)");
        mainViewModel.switchMode(RationalBase);
        mainViewModel.enterCommand("sqrt(2)");
        REQUIRE(startsWith(mainViewModel.getPrimaryText().c_str(), "1.41"));
        REQUIRE("Real" == mainViewModel.getSecondaryText());
    }

    SECTION("spawning a PreciseOutputViewModel") {
        mainViewModel.enterCommand("pi");
        PreciseOutputViewModel preciseOutputViewModel = mainViewModel.spawnPreciseOutputViewModel();
        REQUIRE("3.1415926536" == preciseOutputViewModel.getResult());

        // TODO: same output immediately after initialisation

        SECTION("reevaluation with same precision does not change output") {
            preciseOutputViewModel.setPrecision(10);
            REQUIRE(mainViewModel.getPrimaryText()
                    == preciseOutputViewModel.getResult());
        }

        // TODO: rewrite these for significant digits, when this is done
        // also check the value itself
        SECTION("reevaluation with larger precision") {
            preciseOutputViewModel.setPrecision(50);
            REQUIRE("3.14159265358979323846264338327950288419716939937511"
                    == preciseOutputViewModel.getResult());
        }
        SECTION("reevaluation with smaller precision") {
            preciseOutputViewModel.setPrecision(5);
            REQUIRE("3.14159" == preciseOutputViewModel.getResult());
        }
    }

    SECTION("main view model remains functional after destruction of the precise output view model") {
        // let's put the spawned view model in a block;
        // that will destruct it
        {
            mainViewModel.enterCommand("pi");
            PreciseOutputViewModel PreciseOutputViewModel = mainViewModel.spawnPreciseOutputViewModel();
        }
        mainViewModel.enterCommand("e");
        REQUIRE(startsWith(mainViewModel.getPrimaryText().c_str(), "2.71"));
    }
}
