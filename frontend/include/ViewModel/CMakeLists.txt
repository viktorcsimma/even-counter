target_sources(
    calc
    PRIVATE MainViewModel.hpp AsyncCalculationAlreadyInProgressException.hpp
)
target_sources(
    test
    PRIVATE MainViewModel.hpp
)
