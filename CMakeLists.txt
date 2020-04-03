cmake_minimum_required(VERSION 3.6 FATAL_ERROR)

list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

cmake_host_system_information(RESULT CORE_COUNT QUERY NUMBER_OF_LOGICAL_CORES)
set(CMAKE_VERBOSE_MAKEFILE true CACHE BOOL "")
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "-Wall -Wextra \
        -Wdouble-promotion \
        -Wformat=2 \
        -Wno-variadic-macros \
        -Wcast-align \
        -Wstrict-aliasing=2 \
        -Wstrict-overflow=5 \
        -Wfloat-equal \
        -Wwrite-strings \
        -Wno-missing-braces \
        -Wno-parentheses-equality") #-Werror

set(USED_CMAKE_GENERATOR "${CMAKE_GENERATOR}" CACHE STRING "Expose CMAKE_GENERATOR" FORCE)
if (USED_CMAKE_GENERATOR MATCHES "Ninja")
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color=always")
endif ()

set(CMAKE_CXX_FLAGS_DEBUG "-g -O0 --coverage")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release")
endif ()

################################################################################
option(BUILD_JSLIB "Build JS version of TML library" OFF)
if (BUILD_JSLIB)
    list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_LIST_DIR}/cmake)
    include(emscripten_toolchain)
    set_emscripten_toolchain()
endif ()
################################################################################

project(tml)

if (BUILD_JSLIB)
    if (EMSCRIPTEN)
        add_subdirectory("js")
    endif ()
else ()
    add_subdirectory("src")
endif ()

set(BUILD_TESTS ON CACHE STRING "build the tml test suite ON")
set_property(CACHE BUILD_TESTS PROPERTY STRINGS "OFF" "ON")

# Testing

if (BUILD_TESTS)
    set(DOCTEST_HEADER "${PROJECT_SOURCE_DIR}/src/doctest.h" CACHE PATH "Doctest header")
    if (NOT EXISTS "${DOCTEST_HEADER}")
        message(STATUS "Downloading doctest to '${PROJECT_SOURCE_DIR}'")
        find_package(Wget REQUIRED)
        execute_process(COMMAND "${WGET_EXECUTABLE}" https://raw.githubusercontent.com/onqtam/doctest/master/doctest/doctest.h -P ${PROJECT_SOURCE_DIR}/src)
    endif ()

    add_library(doctest INTERFACE)
    target_compile_definitions(doctest INTERFACE TML_USE_DOCTEST)
    set(TEST_FRAMEWORK doctest)

    enable_testing()
    add_subdirectory(tests)
endif ()

option(BUILD_CLANG_TIDY "Run clang tidy" FALSE)
option(BUILD_CLANG_FORMAT "Run clang format" FALSE)
option(BUILD_CPPCHECK "Run cppcheck" FALSE)
option(BUILD_CODE_COVERAGE "Generate code coverage" FALSE)

message(STATUS "CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE}")

if (CMAKE_BUILD_TYPE STREQUAL "Debug")
    message(STATUS "CMAKE_CXX_COMPILER_ID ${CMAKE_CXX_COMPILER_ID}")
    message(STATUS "CMAKE_CXX_COMPILER ${CMAKE_CXX_COMPILER}")

    if (BUILD_CLANG_TIDY AND CMAKE_CXX_COMPILER_ID MATCHES "Clang")
        include(clang-tidy)
    endif ()

    if (BUILD_CLANG_FORMAT AND CMAKE_CXX_COMPILER_ID MATCHES "Clang")
        include(clang-format)
    endif ()

    if (BUILD_CPPCHECK)
        message(STATUS "Including cppcheck")
        include(cppcheck)
    endif ()

    if (BUILD_CODE_COVERAGE)
        message(STATUS "Including code coverage")
        include(code-coverage)
    endif ()
endif ()
