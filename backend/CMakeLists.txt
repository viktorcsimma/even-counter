project(Acorn)

# add_library(Acorn src/All.agda src/acornInterruptEvaluation.c)
# add_library(Acorn::Acorn ALIAS Acorn)

# add_executable(AcornShell src/All.agda src/Main.hs)

# preparing the library to be used by other projects
# make cache variables for install destinations
include(GNUInstallDirs)
# now, we put our headers in the include/ folder
# adding project root as an include directory
target_include_directories(Acorn
                           PUBLIC
                           "$<BUILD_INTERFACE:${BACKEND_DIR}/include>"
                           "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>"
)
install(FILES "${BACKEND_DIR}/include/TinyHsFFI.h" "${BACKEND_DIR}/include/Acorn.h" DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

# For some reason, on Windows, Interaction.o gets corrupted when copied into the library;
# so it has to be included separately.
# It can be imported like this:
# target_link_libraries(calc PRIVATE "${CMAKE_INSTALL_PREFIX}/../Acorn/lib/Interaction.o")
# (not too elegant, but it works).
# See my own question at
# https://stackoverflow.com/questions/78260754/ghc-staticlib-with-ffi-on-windows-tries-to-link-an-executable-with-foreign-ex/78261321#78261321.
if("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
  install(FILES "${BACKEND_DIR}/src/Shell/Interaction.o" DESTINATION ${CMAKE_INSTALL_LIBDIR})

endif()
install(TARGETS Acorn
        EXPORT AcornTargets
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
# see https://stackoverflow.com/questions/55635294/how-to-create-packages-with-cmake

install(
  EXPORT AcornTargets
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Acorn
  NAMESPACE Acorn::
  # FILE AcornTargets.cmake # Not sure if this is still needed
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

