cmake_minimum_required(VERSION 3.6 FATAL_ERROR)

list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

cmake_host_system_information(RESULT CORE_COUNT QUERY NUMBER_OF_LOGICAL_CORES)
set(CMAKE_VERBOSE_MAKEFILE true CACHE BOOL "")

set(USED_CMAKE_GENERATOR "${CMAKE_GENERATOR}" CACHE STRING "Expose CMAKE_GENERATOR" FORCE)
if (USED_CMAKE_GENERATOR MATCHES "Ninja")
	SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color=always")
endif ()

if (NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif ()

################################################################################
#option(WITH_Z3 "use Z3" FALSE)
option(WITH_THREADS "use Threads" TRUE)
option(WITH_BOOST "use Boost" FALSE)
option(WITH_WCHAR "use wchar_t for system calls (instead of char)" FALSE)
option(WITH_EXCEPTIONS "use exceptions" FALSE)
################################################################################

################################################################################
option(BUILD_DOC "Build documentation" OFF)
# check if Doxygen is installed
find_package(Doxygen)
if (DOXYGEN_FOUND AND BUILD_DOC)
    # set input and output files
    set(DOXYGEN_IN ${CMAKE_CURRENT_SOURCE_DIR}/docs/Doxyfile.in)
    set(DOXYGEN_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

    # request to configure the file
    configure_file(${DOXYGEN_IN} ${DOXYGEN_OUT} @ONLY)
    message("Doxygen build started")

    # note the option ALL which allows to build the docs together with the application
    add_custom_target( doc_doxygen ALL
        COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUT}
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        COMMENT "Generating API documentation with Doxygen"
        VERBATIM )
else (DOXYGEN_FOUND AND BUILD_DOC)
  message("Doxygen need to be installed to generate the doxygen documentation")
endif (DOXYGEN_FOUND AND BUILD_DOC)
################################################################################

################################################################################
option(BUILD_JSLIB "Build JS version of TML library" OFF)
option(BUILD_JSMODULE "Build JS version of TML library (ES6 module)" OFF)
if (BUILD_JSMODULE)
	set(BUILD_JSLIB ON CACHE STRING "")
endif ()
if (BUILD_JSLIB)
	list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_LIST_DIR}/cmake)
	include(emscripten_toolchain)
	set_emscripten_toolchain()
	set(BUILD_TESTS OFF CACHE STRING "")         # no automated tests
	set(BUILD_CODE_COVERAGE OFF CACHE STRING "") # no coverage
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
option(BUILD_TML_CHECK "Build TML parsing check" TRUE)

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
		find_program(GCOVR gcovr)
		if (GCOVR)
			message(STATUS "Including code coverage")
			set(CMAKE_CXX_FLAGS "-g -O0 -fprofile-arcs -ftest-coverage" CACHE STRING "Code coverage CXX options" FORCE)
			include(code-coverage)
			append_coverage_compiler_flags()
		else ()
			message(WARNING "Gcovr not found!")
		endif ()
	endif ()

	if (BUILD_TML_CHECK)
		message(STATUS "Including tml parsing check")
		include(tml-check)
	endif ()
endif ()
