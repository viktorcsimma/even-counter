cmake_minimum_required(VERSION 3.9)

# the language is given so that GNUInstallDirs knows where to install
project(Acorn)

add_library(Acorn src/All.agda src/acornInterruptEvaluation.c include/TinyHsFFI.h include/Future.h include/Acorn.h)
add_library(Acorn::Acorn ALIAS Acorn)

add_executable(AcornShell src/All.agda src/Main.hs)

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

# for solving encoding problems on Windows
if("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
    set(WINDOWS_ENCODING_COMMAND "CHCP 65001")
endif()

# The library needs a -threaded option so as to be able to interrupt a thread from another by a foreign call.
set(CMAKE_Agda_CREATE_STATIC_LIBRARY
      "${WINDOWS_ENCODING_COMMAND}"
      # TODO: -v2 output gets hidden in Qt Creator unless an error occurs; get it shown
      "agda2hs -v2 ${CMAKE_CURRENT_SOURCE_DIR}/src/All.agda -o ${CMAKE_CURRENT_BINARY_DIR}/build/hs"
      # we have to let ghc also find those files in src that are already written in Haskell
      "ghc -threaded --make \
          -i${CMAKE_CURRENT_BINARY_DIR}/build/hs:${CMAKE_CURRENT_SOURCE_DIR}/src \
          -hidir ${CMAKE_CURRENT_BINARY_DIR}/build/hi -odir ${CMAKE_CURRENT_BINARY_DIR}/build/o -stubdir ${CMAKE_CURRENT_BINARY_DIR}/build/stub \
          -staticlib -fPIC -optl-pthread -optl-static \
          -o ${CMAKE_CURRENT_BINARY_DIR}/libAcorn.a \
          ${CMAKE_CURRENT_BINARY_DIR}/build/hs/All.hs ${CMAKE_CURRENT_SOURCE_DIR}/src/acornInterruptEvaluation.c"
)
set(CMAKE_Agda_LINK_EXECUTABLE
      "${WINDOWS_ENCODING_COMMAND}"
      "agda2hs -v2 ${CMAKE_CURRENT_SOURCE_DIR}/src/All.agda -o ${CMAKE_CURRENT_BINARY_DIR}/build/hs"
      # we have to let ghc also find those files in src that are already written in Haskell
      "ghc --make \
          -i${CMAKE_CURRENT_BINARY_DIR}/build/hs:${CMAKE_CURRENT_SOURCE_DIR}/src \
          -hidir ${CMAKE_CURRENT_BINARY_DIR}/build/hi -odir ${CMAKE_CURRENT_BINARY_DIR}/build/o -stubdir ${CMAKE_CURRENT_BINARY_DIR}/build/stub \
          -o ${CMAKE_CURRENT_BINARY_DIR}/AcornShell \
          ${CMAKE_CURRENT_SOURCE_DIR}/src/Main.hs"
)
# we provide for CMake to erase these on cleaning
file (GLOB_RECURSE CLEAN_FILES LIST_DIRECTORIES true "${CMAKE_CURRENT_BINARY_DIR}/build/*")
set_target_properties(Acorn
    PROPERTIES ADDITIONAL_CLEAN_FILES "${CLEAN_FILES}")
set_target_properties(AcornShell
    PROPERTIES ADDITIONAL_CLEAN_FILES "${CLEAN_FILES}")

# preparing the library to be used by other projects
# make cache variables for install destinations
include(GNUInstallDirs)

# now, we put our headers in the include/ folder
# adding project root as an include directory
target_include_directories(Acorn
                           PUBLIC
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
                           "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>"
)
install(FILES include/TinyHsFFI.h include/Future.h include/Acorn.h DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

# For some reason, on Windows, Interaction.o gets corrupted when copied into the library;
# so it has to be included separately.
# It can be imported like this:
# target_link_libraries(calc PRIVATE "${CMAKE_INSTALL_PREFIX}/../Acorn/lib/Interaction.o")
# (not too elegant, but it works).
# See my own question at
# https://stackoverflow.com/questions/78260754/ghc-staticlib-with-ffi-on-windows-tries-to-link-an-executable-with-foreign-ex/78261321#78261321.
if("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
  install(FILES src/Shell/Interaction.o DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif()


# see https://stackoverflow.com/questions/55635294/how-to-create-packages-with-cmake

install(TARGETS Acorn
        EXPORT AcornTargets
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
install(
        EXPORT AcornTargets
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Acorn
        NAMESPACE Acorn::
        FILE AcornTargets.cmake # Not sure if this is still needed
)

include(CMakePackageConfigHelpers)
configure_package_config_file(
  "Config.cmake.in"
  "AcornConfig.cmake"
  INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Acorn
  PATH_VARS
    CMAKE_INSTALL_LIBDIR
  )

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/AcornConfigVersion.cmake
  VERSION 0.1
  COMPATIBILITY SameMinorVersion
  )

# install Config and ConfigVersion files
install(
  FILES "${CMAKE_CURRENT_BINARY_DIR}/AcornConfig.cmake"
        "${CMAKE_CURRENT_BINARY_DIR}/AcornConfigVersion.cmake"
  DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/Acorn"
  )

