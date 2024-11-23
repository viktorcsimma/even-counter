target_sources(
    calc
    PRIVATE HsAppStateWrapper.hpp MainViewModel.hpp Future.hpp AsyncCalculationAlreadyInProgressException.hpp
)
target_sources(
    test
    PRIVATE HsAppStateWrapper.hpp MainViewModel.hpp
)
