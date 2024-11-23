cmake_minimum_required(VERSION 3.9)

project(EvenCounter)

set(PROJECT_VERSION 0.1)
set(PROJECT_VERSION_MAJOR 0)
set(PROJECT-NAME_VERSION_MINOR 1)

# this will tell the subprojects that we are compiling from the large project
set(NOT_TOP_LEVEL True)

add_subdirectory(backend)
add_subdirectory(frontend)

