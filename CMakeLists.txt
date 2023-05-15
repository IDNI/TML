set(CMAKE_VERBOSE_MAKEFILE ON)
set(CMAKE_VERBOSE_MAKEFILE true CACHE BOOL "")
cmake_minimum_required(VERSION 3.6 FATAL_ERROR)
cmake_host_system_information(RESULT CORE_COUNT QUERY NUMBER_OF_LOGICAL_CORES)
set(USED_CMAKE_GENERATOR "${CMAKE_GENERATOR}" CACHE STRING "Expose CMAKE_GENERATOR" FORCE)
if(USED_CMAKE_GENERATOR MATCHES "Ninja")
	SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color=always")
endif()
if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()
list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_LIST_DIR}/cmake)
################################################################################
set(namespace "idni")
set(PROJECT_SHORT_NAME tml)
project("${namespace}_${PROJECT_SHORT_NAME}"
	VERSION 0.0.1
	DESCRIPTION "TML - Tau Meta Language"
	)
################################################################################
option(WITH_THREADS "use Threads" TRUE)
option(WITH_BOOST "use Boost" FALSE)
option(WITH_EXCEPTIONS "use exceptions" FALSE)
################################################################################
option(BUILD_SHARED_LIBRARY "Build shared library" FALSE)
option(BUILD_STATIC_LIBRARY "Build static library" FALSE)
option(BUILD_EXECUTABLE "Build executable" FALSE)
option(BUILD_SHARED_EXECUTABLE "Build executable using shared library" FALSE)
option(BUILD_TESTS "Build tests of TML" TRUE)
option(BUILD_JSLIB "Build JS version of TML library" FALSE)
option(BUILD_JSMODULE "Build JS version of TML library (ES6 module)" OFF)
option(BUILD_CLANG_TIDY "Run clang tidy" FALSE)
option(BUILD_CLANG_FORMAT "Run clang format" FALSE)
option(BUILD_CPPCHECK "Run cppcheck" FALSE)
option(BUILD_CODE_COVERAGE "Generate code coverage" FALSE)
option(BUILD_TML_CHECK "Build TML parsing check" FALSE)
################################################################################
if(BUILD_JSMODULE)
	set(BUILD_JSLIB ON CACHE STRING "")
endif ()
if(BUILD_JSLIB)
	set(BUILD_STATIC_LIBRARY FALSE)
	set(BUILD_SHARED_LIBRARY FALSE)
	set(BUILD_EXECUTABLE FALSE)
	set(BUILD_SHARED_EXECUTABLE FALSE)
	set(BUILD_TESTS OFF CACHE STRING "")         # no automated tests
	set(BUILD_CODE_COVERAGE OFF CACHE STRING "") # no coverage
	set(EMSCRIPTEN_CMAKE "${EMSCRIPTEN_DIR}/cmake/Modules/Platform/Emscripten.cmake")
	if(EXISTS "${EMSCRIPTEN_CMAKE}")
		set(EMSCRIPTEN_ROOT_PATH "${EMSCRIPTEN_DIR}")
		set(CMAKE_TOOLCHAIN_FILE "${EMSCRIPTEN_CMAKE}" CACHE STRING "")
	else()
		message(SEND_ERROR "emscripten not found in '${EMSCRIPTEN_DIR}'. Use -DEMSCRIPTEN_DIR=<emscripten_install_directory>.")
	endif()
endif()
if(NOT BUILD_STATIC_LIBRARY)
	if(NOT BUILD_SHARED_LIBRARY)
		if(NOT BUILD_SHARED_EXECUTABLE)
			if(NOT BUILD_TESTS)
				if(NOT BUILD_JSLIB)
					if(NOT BUILD_EXECUTABLE)
						set(BUILD_EXECUTABLE TRUE)
					endif()
				endif()
			endif()
		endif()
	endif()
endif()
################################################################################
message(STATUS "EMSCRIPTEN: ${EMSCRIPTEN}")
message(STATUS "WITH_THREADS: ${WITH_THREADS}")
message(STATUS "WITH_BOOST: ${WITH_BOOST}")
message(STATUS "WITH_EXCEPTIONS: ${WITH_EXCEPTIONS}")
message(STATUS "BUILD_SHARED_LIBRARY: ${BUILD_SHARED_LIBRARY}")
message(STATUS "BUILD_STATIC_LIBRARY: ${BUILD_STATIC_LIBRARY}")
message(STATUS "BUILD_EXECUTABLE: ${BUILD_EXECUTABLE}")
message(STATUS "BUILD_SHARED_EXECUTABLE: ${BUILD_SHARED_EXECUTABLE}")
message(STATUS "BUILD_TESTS: ${BUILD_TESTS}")
message(STATUS "BUILD_JSLIB: ${BUILD_JSLIB}")
message(STATUS "BUILD_JSMODULE: ${BUILD_JSMODULE}")
message(STATUS "BUILD_CLANG_TIDY: ${BUILD_CLANG_TIDY}")
message(STATUS "BUILD_CLANG_FORMAT: ${BUILD_CLANG_FORMAT}")
message(STATUS "BUILD_CPPCHECK: ${BUILD_CPPCHECK}")
message(STATUS "BUILD_CODE_COVERAGE: ${BUILD_CODE_COVERAGE}")
message(STATUS "BUILD_TML_CHECK: ${BUILD_TML_CHECK}")
################################################################################
set(PROJECT_HEADERS
	src/builtins.h
	src/cpp_gen.h
	src/defs.h
	src/dict.h
	src/driver.h
	src/err.h
	src/fof.h
	src/form.h
	src/input.h
	src/ir_builder.h
	src/iterators.h
	src/options.h
	src/output.h
	src/printing.h
	src/tables.h
	src/tables_progress.h
	src/transform_opt_common.h
	src/transform_opt_cqc.h
	src/transform_opt_squaring.h
	src/typemanager.h
)
set(PROJECT_SOURCES
	src/builtins.cpp
	src/cpp_gen.cpp
	src/dict.cpp
	src/driver.cpp
	src/fof.cpp
	src/form.cpp
	src/input.cpp
	src/iterators.cpp
	src/ir_builder.cpp
	src/options.cpp
	src/output.cpp
	src/printing.cpp
	src/proof.cpp
	src/save_csv.cpp
	src/tables.cpp
	src/tables_builtins.cpp
	src/tables_ext.cpp
	src/tables_printer.cpp
	src/tables_progress.cpp
	src/tml_earley.cpp
	src/transform.cpp
	src/transform_bitunv.cpp
	src/transform_guards.cpp
	src/transform_opt.cpp
	src/transform_opt_cqc.cpp
	src/transform_opt_squaring.cpp
	src/typemanager.cpp
	src/utils.cpp
)
if(WITH_THREADS)
	set(CLI_SOURCES src/main.cpp src/repl.cpp)
else()
	set(CLI_SOURCES src/main.cpp)
endif()
include(idni-common)
include(git-defs)
################################################################################
function(target_pass_features_on target)
	if(WITH_THREADS)
		target_compile_definitions(${target} PRIVATE "-DWITH_THREADS")
		target_link_libraries(${target} Threads::Threads)
	endif()
	if(WITH_WCHAR)
		target_compile_definitions(${target} PRIVATE "-DWITH_WCHAR")
	endif()
	if(WITH_EXCEPTIONS)
		target_compile_definitions(${target} PRIVATE "-DWITH_EXCEPTIONS")
	endif()
	target_compile_definitions(${target} PRIVATE "-DWITH_ARITH")
	target_compile_definitions(${target} PRIVATE "-DWITH_MMAP")
	target_git_definitions(${target})
endfunction()
################################################################################
find_library(Z3 NAMES z3)
add_library(Z3 SHARED IMPORTED)
set_target_properties(Z3 PROPERTIES IMPORTED_LOCATION "${Z3}")
target_link_libraries(${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object Z3)
target_compile_definitions(${OBJECT_LIB_NAME} PRIVATE "-DWITH_Z3")
target_pass_features_on(${OBJECT_LIB_NAME})

if(WITH_THREADS)
	set(THREADS_PREFER_PTHREAD_FLAG ON)
	find_package(Threads)
endif()

if(WITH_BOOST)
	target_compile_definitions(${OBJECT_LIB_NAME} PRIVATE "-DWITH_BOOST")
	find_package(Boost COMPONENTS system thread REQUIRED)
	if(Boost_FOUND)
		target_include_directories(${OBJECT_LIB_NAME}
			PRIVATE ${Boost_INCLUDE_DIRS}
		)
		target_link_libraries(${OBJECT_LIB_NAME}
			Boost::boost Boost::system
		)
	endif(Boost_FOUND)
endif()

if(BUILD_STATIC_LIBRARY)
	target_pass_features_on(${STATIC_LIB_NAME})
endif()

if(BUILD_SHARED_LIBRARY)
	target_pass_features_on(${SHARED_LIB_NAME})
endif()

if(BUILD_EXECUTABLE)
	add_executable(${EXECUTABLE_NAME})
	target_setup(${EXECUTABLE_NAME})
	target_pass_features_on(${EXECUTABLE_NAME})
	target_sources(${EXECUTABLE_NAME} PRIVATE ${CLI_SOURCES})
	target_compile_definitions(${EXECUTABLE_NAME}
		PRIVATE "-DWITH_ARITH" "-DWITH_MMAP"
	)
	target_link_libraries(${EXECUTABLE_NAME}
		${OBJECT_LIB_NAME} idni_bdd_object idni_parser_object)
	target_include_directories(${EXECUTABLE_NAME} PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/bdd/src>
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/parser>
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/parser/src>)
	if(BUILD_CODE_COVERAGE)
		target_link_libraries(${EXECUTABLE_NAME} gcov)
	endif()
endif()

if(BUILD_SHARED_EXECUTABLE)
	add_executable(${EXE_SHARED_NAME})
	target_setup(${EXE_SHARED_NAME})
	target_pass_features_on(${EXE_SHARED_NAME})
	target_sources(${EXE_SHARED_NAME} PRIVATE ${CLI_SOURCES})
	target_compile_definitions(${EXE_SHARED_NAME}
		PRIVATE "-DWITH_ARITH" "-DWITH_MMAP"
	)
	target_link_libraries(${EXE_SHARED_NAME}
		${SHARED_LIB_NAME} idni_bdd_object idni_parser_object)
	target_include_directories(${EXE_SHARED_NAME} PUBLIC
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/bdd/src>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/parser>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/parser/src>)
	if(BUILD_CODE_COVERAGE)
		target_link_libraries(${EXE_SHARED_NAME} gcov)
	endif()
endif()

################################################################################
if(BUILD_JSLIB)
	list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_LIST_DIR}/cmake)
	include(emscripten_toolchain)
	set_emscripten_toolchain()
	exclude(${OBJECT_LIB_NAME})
	add_subdirectory("js")
else()
	include(add_git_submodule)
	set(WITH_DEVHELPERS TRUE CACHE BOOL "")
	add_git_submodule(external/parser)
	set(WITH_ARITH TRUE CACHE BOOL "")
	set(WITH_MMAP TRUE CACHE BOOL "")
	add_git_submodule(external/bdd)
	include(installation)
endif()

################################################################################
# Testing
if(BUILD_TESTS)
	set(DOCTEST_HEADER "${PROJECT_SOURCE_DIR}/src/doctest.h"
		CACHE PATH "Doctest header"
	)
	if(NOT EXISTS "${DOCTEST_HEADER}")
		message(STATUS "Downloading doctest to '${PROJECT_SOURCE_DIR}'")
		find_package(Wget REQUIRED)
		execute_process(COMMAND "${WGET_EXECUTABLE}"
			https://raw.githubusercontent.com/onqtam/doctest/master/doctest/doctest.h
			-P ${PROJECT_SOURCE_DIR}/src
		)
	endif()
	add_library(doctest INTERFACE)
	target_compile_definitions(doctest INTERFACE TML_USE_DOCTEST)
	target_include_directories(doctest INTERFACE
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/bdd/src>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/parser>
		$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/external/parser/src>)
	set(TEST_FRAMEWORK doctest)
	enable_testing()
	add_subdirectory(tests)
endif()

################################################################################
# check if Doxygen is installed and generate a documentation
find_package(Doxygen)
if(DOXYGEN_FOUND AND BUILD_DOC)
	# set input and output files
	set(DOXYGEN_IN ${CMAKE_CURRENT_SOURCE_DIR}/docs/Doxyfile.in)
	set(DOXYGEN_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

	# request to configure the file
	configure_file(${DOXYGEN_IN} ${DOXYGEN_OUT} @ONLY)
	message("Doxygen build started")

	# note the option ALL which allows to build the docs together with the application
	add_custom_target(doc_doxygen ALL
		COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUT}
		WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
		COMMENT "Generating API documentation with Doxygen"
		VERBATIM)
else(DOXYGEN_FOUND AND BUILD_DOC)
	message("Doxygen need to be installed to generate the doxygen documentation")
endif(DOXYGEN_FOUND AND BUILD_DOC)
