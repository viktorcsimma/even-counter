#include "Backend/HsAppStateWrapper.hpp"

#include <catch2/catch_test_macros.hpp>

#include <catch2/reporters/catch_reporter_event_listener.hpp>
#include <catch2/reporters/catch_reporter_registrars.hpp>

// Two very simple tests for demonstration.

TEST_CASE("HsAppStateWrapper") {
    HsAppStateWrapper appStateWrapper;
    REQUIRE(0 == appStateWrapper.getCounterValue());
    
    SECTION("adding even numbers to the counter") {
        appStateWrapper.incrementWith(2);
        REQUIRE(2 == appStateWrapper.getCounterValue());
        appStateWrapper.incrementWith(-10);
        REQUIRE(-8 == appStateWrapper.getCounterValue());
    }

    SECTION("trying to add odd numbers to the counter") {
        REQUIRE(!appStateWrapper.incrementWith(1));
        REQUIRE(0 == appStateWrapper.getCounterValue());
        REQUIRE(!appStateWrapper.incrementWith(9));
        REQUIRE(0 == appStateWrapper.getCounterValue());
        REQUIRE(!appStateWrapper.incrementWith(-1));
        REQUIRE(0 == appStateWrapper.getCounterValue());
        REQUIRE(!appStateWrapper.incrementWith(-3));
        REQUIRE(0 == appStateWrapper.getCounterValue());
    }
}
