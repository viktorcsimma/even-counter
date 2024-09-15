// A custom main function
// that also initialises the Haskell runtime
// before the tests
// and shuts it down in the end.

#include "TinyHsFFI.h"
#include <catch2/catch_session.hpp>

int main( int argc, char* argv[] ) {
    hs_init(&argc, &argv);
    int result = Catch::Session().run( argc, argv );
    hs_exit();
    return result;
}
