cmake_minimum_required (VERSION 3.16)

set(TS_FILES src/View/calc_en_GB.ts)

add_dependencies(calc Acorn)
add_dependencies(test Acorn)

# afterwards:

# see https://crascit.com/2016/01/31/enhanced-source-file-handling-with-target_sources/ for the technique
add_subdirectory(src)
add_subdirectory(include)
# should we also add headers later? it helps IDEs

target_link_libraries(calc PRIVATE Qt${QT_VERSION_MAJOR}::Widgets)

target_link_libraries(test PRIVATE Catch2::Catch2)

set(CMAKE_PREFIX_PATH "${CMAKE_PREFIX_PATH}:${BACKEND_DIR}")

# target_link_libraries(calc PRIVATE ${BACKEND_DIR}/libAcorn.a)
target_include_directories(calc PRIVATE "${BACKEND_DIR}/include")
target_link_libraries(test PRIVATE Acorn::Acorn)
target_include_directories(test PRIVATE Acorn::include)

# For some reason, on Windows, Interaction.o gets corrupted when copied into the library;
# so it has to be included separately.
# See my own question at
# https://stackoverflow.com/questions/78260754/ghc-libraries-with-ffi-on-windows-have-foreign-export-symbols-missing.
if("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
  target_link_libraries(calc PRIVATE "${CMAKE_INSTALL_PREFIX}/../Acorn/lib/Interaction.o")
  target_link_libraries(test PRIVATE "${CMAKE_INSTALL_PREFIX}/../Acorn/lib/Interaction.o")
endif()

target_include_directories(calc
                           PUBLIC
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
                           "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>"
)

target_include_directories(test
                           PUBLIC
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
                           "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>"
)

# I don't know why, but with these options, it does not link some system libraries by itself;
# so they need to be named explicitly.
if("Linux" STREQUAL ${CMAKE_SYSTEM_NAME} OR "Darwin" STREQUAL ${CMAKE_SYSTEM_NAME})
  target_link_options(calc PRIVATE -no-pie)
  target_link_options(test PRIVATE -no-pie)
  target_link_libraries(calc PRIVATE dl pthread gmp)
  target_link_libraries(test PRIVATE dl pthread gmp)
  if(CMAKE_BUILD_TYPE MATCHES RELEASE)
      # we tell the dynamic linker to search for shared libraries in the folder of the executable itself
      # this way, we can bundle the remaining libraries with the application
      target_link_options(calc PRIVATE -rpath=.)
  endif()
elseif("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
  target_link_options(calc PRIVATE -pthread -fno-PIC)
  target_link_options(test PRIVATE -pthread -fno-PIC)
  # as flags, they would be added to the beginning of the command, where they get optimised out
  # see the documentation of ld
  target_link_libraries(calc PRIVATE ntdll rpcrt4 dbghelp ucrt msvcrt)
  target_link_libraries(test PRIVATE ws2_32 ntdll rpcrt4 dbghelp ucrt winmm)
else()
  message( FATAL_ERROR "Unsupported operating system: ${CMAKE_SYSTEM_NAME}" )
endif()

# copying assets
file(COPY assets DESTINATION ${CMAKE_BINARY_DIR})
# and installing them, if it is about an installation
install(DIRECTORY assets DESTINATION ${CMAKE_BINARY_DIR})

install(TARGETS calc
    BUNDLE DESTINATION .
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)


if(QT_VERSION_MAJOR EQUAL 6)
    qt_finalize_executable(calc)
endif()
