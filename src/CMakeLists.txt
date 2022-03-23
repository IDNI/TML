cmake_minimum_required(VERSION 3.13)
set(CMAKE_VERBOSE_MAKEFILE true)

project(tml)

if(CMAKE_CONFIGURATION_TYPES)
	set(CMAKE_CONFIGURATION_TYPES Debug Release PgoScan PgoRun)
	set(CMAKE_CONFIGURATION_TYPES
		"${CMAKE_CONFIGURATION_TYPES}" CACHE STRING "" FORCE
	)
endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(TML_DIR "${CMAKE_CURRENT_SOURCE_DIR}/..")
list(APPEND CMAKE_MODULE_PATH ${TML_DIR}/cmake)
include(tml-common)

set(TML_HEADERS
	bdd.h
	builtins.h
	char_defs.h
	defs.h
	dict.h
	driver.h
	err.h
	form.h
	input.h
	memory_map.h
	options.h
	output.h
	tables.h
	ir_builder.h
	typemanager.h
)

set(TML_SOURCES
	bdd.cpp
	bdd_ext.cpp
	builtins.cpp
	dict.cpp
	driver.cpp
	form.cpp
	input.cpp
	options.cpp
	output.cpp
	proof.cpp
	save_csv.cpp
	tables.cpp
	tables_builtins.cpp
	tables_ext.cpp
	transform.cpp
	transform_guards.cpp
	utils.cpp
	ir_builder.cpp
	typemanager.cpp
	transform_bitunv.cpp
)

if (WITH_THREADS)
	set(CLI_HEADERS async_reader.h repl.h udp.h)
	set(CLI_SOURCES main.cpp repl.cpp)
else()
	set(CLI_SOURCES main.cpp)
endif()

set(TML_DEBUG_OPTIONS "-O0;-DDEBUG;-ggdb3")
set(TML_RELEASE_OPTIONS "-O3;-DNDEBUG")

set(TML_PGO_DIR "${PROJECT_BINARY_DIR}/pgo")
set(TML_PGO_OPTIONS
	"$<IF:$<OR:$<CONFIG:PgoScan>,$<CONFIG:PgoRun>>,-fprofile-dir=${TML_PGO_DIR},>"
	"$<$<CONFIG:PgoScan>:-fprofile-generate=${TML_PGO_DIR}>"
	"$<$<CONFIG:PgoRun>:-fprofile-use=${TML_PGO_DIR}>"
)

set(TML_COMPILE_OPTIONS
	"$<IF:$<CONFIG:Debug>,${TML_DEBUG_OPTIONS},${TML_RELEASE_OPTIONS}>"
	"$<$<CONFIG:Release>:-flto>"
	${TML_PGO_OPTIONS}
)
set(TML_LINK_OPTIONS ${TML_PGO_OPTIONS})
if (BUILD_CODE_COVERAGE)
	set(TML_DEBUG_OPTIONS "${TML_DEBUG_OPTIONS}" --coverage)
	set(TML_RELEASE_OPTIONS "${TML_RELEASE_OPTIONS}" --coverage)
endif ()

# object library
#################
add_library(TMLo OBJECT)
target_setup(TMLo)
target_compile_options(TMLo     PRIVATE ${TML_COMPILE_OPTIONS} -fPIC)
target_link_options(TMLo        PRIVATE ${TML_LINK_OPTIONS})
target_sources(TMLo             PRIVATE ${TML_SOURCES} ${TML_HEADERS})
target_link_libraries(TMLo      ${CMAKE_THREAD_LIBS_INIT})
target_include_directories(TMLo PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)
if (WITH_THREADS)
	target_compile_definitions(TMLo PRIVATE "-DWITH_THREADS")
endif ()
if (WITH_WCHAR)
	target_compile_definitions(TMLo PRIVATE "-DWITH_WCHAR")
endif ()
if (WITH_EXCEPTIONS)
	target_compile_definitions(TMLo PRIVATE "-DWITH_EXCEPTIONS")
endif ()

# boost
###########
if (WITH_BOOST)
	target_compile_definitions(TMLo PRIVATE "-DWITH_BOOST")
	find_package(Boost COMPONENTS system thread REQUIRED)
	if (Boost_FOUND)
		target_include_directories(TMLo PRIVATE ${Boost_INCLUDE_DIRS})
		target_link_libraries(TMLo Boost::boost Boost::system)
	endif (Boost_FOUND)
endif ()

# pthreads
###########
if (WITH_THREADS)
	set(THREADS_PREFER_PTHREAD_FLAG ON)
	find_package(Threads)
endif()

# z3 library
#############
if (WITH_Z3)
	find_library(Z3 NAMES z3)
	add_library(Z3 SHARED IMPORTED)
	set_target_properties(Z3 PROPERTIES
		IMPORTED_LOCATION "${Z3}")
	target_link_libraries(TMLo Z3)
	target_compile_definitions(TMLo PRIVATE "-DWITH_Z3")
endif()


# shared library
#################

add_library(TMLso SHARED)
add_library(TML::TMLso ALIAS TMLso)
target_setup(TMLso)
target_compile_options(TMLso     PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(TMLso        PRIVATE ${TML_LINK_OPTIONS})
target_link_libraries(TMLso      TMLo)
target_include_directories(TMLso PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
	$<INSTALL_INTERFACE:.>
)
set_target_properties(TMLso PROPERTIES
	EXPORT_NAME TMLso
	PUBLIC_HEADER "${TML_HEADERS}"
)


# static library
#################

add_library(TMLs STATIC)
add_library(TML::TMLs ALIAS TMLs)
target_setup(TMLs)
target_compile_options(TMLs     PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(TMLs        PRIVATE ${TML_LINK_OPTIONS})
target_link_libraries(TMLs      TMLo)
target_include_directories(TMLs PUBLIC
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)
set_target_properties(TMLs PROPERTIES OUTPUT_NAME "TML")

# executable
#############

add_executable(tml)
target_setup(tml)
target_compile_options(tml PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(tml    PRIVATE ${TML_LINK_OPTIONS})
target_sources(tml         PRIVATE ${CLI_SOURCES} ${CLI_HEADERS})
target_link_libraries(tml  TMLs)
if (WITH_THREADS)
	target_compile_definitions(tml PRIVATE "-DWITH_THREADS")
	target_link_libraries(tml Threads::Threads)
endif()
if (WITH_WCHAR)
	target_compile_definitions(tml PRIVATE "-DWITH_WCHAR")
endif ()
if (WITH_EXCEPTIONS)
	target_compile_definitions(tml PRIVATE "-DWITH_EXCEPTIONS")
endif ()
if (BUILD_CODE_COVERAGE)
	target_link_libraries(tml gcov)
endif ()

# executable using shared library
##################################

add_executable(tml_shared)
target_setup(tml_shared)
target_compile_options(tml_shared PRIVATE ${TML_COMPILE_OPTIONS})
target_link_options(tml_shared    PRIVATE ${TML_LINK_OPTIONS})
target_sources(tml_shared         PRIVATE ${CLI_SOURCES} ${CLI_HEADERS})
target_link_libraries(tml_shared  TMLso)
if (WITH_THREADS)
	target_compile_definitions(tml_shared PRIVATE "-DWITH_THREADS")
	target_link_libraries(tml_shared Threads::Threads)
endif()
if (WITH_WCHAR)
	target_compile_definitions(tml_shared PRIVATE "-DWITH_WCHAR")
endif ()
if (WITH_EXCEPTIONS)
	target_compile_definitions(tml_shared PRIVATE "-DWITH_EXCEPTIONS")
endif ()
if (BUILD_CODE_COVERAGE)
	target_link_libraries(tml_shared gcov)
endif ()
exclude(tml_shared)


# install
##########

include(GNUInstallDirs)
install(TARGETS tml TMLso TMLo
	EXPORT TML
	LIBRARY       DESTINATION ${CMAKE_INSTALL_LIBDIR}
	PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/TML
	RUNTIME       DESTINATION ${CMAKE_INSTALL_BINDIR}
)
export(EXPORT TML FILE ${TML_DIR}/tml-config.cmake)
install(EXPORT TML DESTINATION ${PROJECT_BINARY_DIR})
