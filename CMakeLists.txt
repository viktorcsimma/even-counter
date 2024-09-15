cmake_minimum_required(VERSION 3.9)

project(Skeleton)

set(PROJECT_VERSION 0.1)
set(PROJECT_VERSION_MAJOR 0)
set(PROJECT-NAME_VERSION_MINOR 1)

include(GNUInstallDirs)

# set(BACKEND_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../backend_install/")

# set(CMAKE_PREFIX_PATH "${CMAKE_PREFIX_PATH};${BACKEND_DIR}")

set(BACKEND_DIR "${CMAKE_CURRENT_SOURCE_DIR}/backend/")

add_library(Acorn "${BACKEND_DIR}/src/All.agda" "${BACKEND_DIR}/src/acornInterruptEvaluation.c")
add_library(Acorn::Acorn ALIAS Acorn)
add_executable(AcornShell "${BACKEND_DIR}/src/All.agda" "${BACKEND_DIR}/src/Main.hs")

# for agda2hs
# "Linking" will be the actual compilation (both with agda2hs and ghc).
# This way, we ensure that there are no additional files and need to copy
# as it was when doing Haskell compilation in `add_custom_command` directives;
# still the Haskell files get updated if the Agda sources are modified.
# (agda2hs will manage what to update.)
# And when running `sudo make install` after building,
# root won't need access to ghc.
set_target_properties(Acorn PROPERTIES
  LINKER_LANGUAGE Agda
)
set_target_properties(AcornShell PROPERTIES
  LINKER_LANGUAGE Agda
)

# The library needs a -threaded option so as to be able to interrupt a thread from another by a foreign call.
set(CMAKE_Agda_CREATE_STATIC_LIBRARY
      "agda2hs ${BACKEND_DIR}/src/All.agda"
      "ghc -threaded --make -i${BACKEND_DIR}/src -staticlib -fPIC -optl-pthread -optl-static -o ${CMAKE_CURRENT_BINARY_DIR}/libAcorn.a ${BACKEND_DIR}/src/All.hs ${BACKEND_DIR}/src/acornInterruptEvaluation.c"
)
set(CMAKE_Agda_LINK_EXECUTABLE
      "agda2hs ${BACKEND_DIR}/src/All.agda"
      "ghc --make -i${BACKEND_DIR}/src -o ${CMAKE_CURRENT_BINARY_DIR}/AcornShell ${BACKEND_DIR}/src/Main.hs"
)

# for Qt

set(CMAKE_AUTOUIC ON)
set(CMAKE_AUTOMOC ON)
set(CMAKE_AUTORCC ON)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(Catch2 REQUIRED)

find_package(QT NAMES Qt6 Qt5 REQUIRED COMPONENTS Core Widgets LinguistTools)
find_package(Qt${QT_VERSION_MAJOR} REQUIRED COMPONENTS Core Widgets LinguistTools)

if(${QT_VERSION_MAJOR} GREATER_EQUAL 6)
    qt_add_executable(calc
        MANUAL_FINALIZATION
        ""


        frontend/include/View/PrimaryLineEdit.h
        frontend/src/View/PrimaryLineEdit.cpp
        frontend/src/View/HistoryItemWidget.ui
        frontend/include/View/HistoryItemWidget.h
        frontend/src/View/HistoryItemWidget.cpp
        frontend/src/View/PreciseOutputWindow.ui
        frontend/include/View/PreciseOutputWindow.h
        frontend/src/View/PreciseOutputWindow.cpp
        frontend/assets/busy_indicator.gif




    )
# Define target properties for Android with Qt 6 as:
#    set_property(TARGET calc APPEND PROPERTY QT_ANDROID_PACKAGE_SOURCE_DIR
#                 ${CMAKE_CURRENT_SOURCE_DIR}/android)
# For more information, see https://doc.qt.io/qt-6/qt-add-executable.html#target-creation

    qt_create_translation(QM_FILES ${CMAKE_SOURCE_DIR} ${TS_FILES})
else()
    if(ANDROID)
        add_library(calc SHARED
            ""
        )
# Define properties for Android with Qt 5 after find_package() calls as:
#    set(ANDROID_PACKAGE_SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/android")
    else()
        add_executable(calc
            ""
        )
    endif()

    qt5_create_translation(QM_FILES ${CMAKE_SOURCE_DIR} ${TS_FILES})
endif()

# this is a simple terminal program
add_executable(test "")

add_subdirectory(backend)
add_subdirectory(frontend)

