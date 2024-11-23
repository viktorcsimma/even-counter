target_sources(
    calc
    PRIVATE HsAppStateWrapper.cpp Future.cpp MainViewModel.cpp
)
target_sources(
    test
    PRIVATE HsAppStateWrapper.cpp
)
