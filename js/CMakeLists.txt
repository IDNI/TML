# This lists file requires CMAKE_TOOLCHAIN_FILE to be set
# to "<EMSCRIPTEN_DIR>/cmake/Modules/Platform/Emscripten.cmake"
# or use emscripten_toolchain module from ../cmake
# This setting must be done before using project()

cmake_minimum_required(VERSION 3.13)

project(tml)

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(tml-common)

set(JSLIB_SOURCES
	../src/bdd.cpp
	../src/bdd.h
	../src/binary.cpp
	../src/defs.h
	../src/dict.cpp
	../src/dict.h
	../src/driver.cpp
	../src/driver.h
	../src/err.h
	../src/input.cpp
	../src/input.h
	../src/options.cpp
	../src/options.h
	../src/output.cpp
	../src/output.h
	../src/print_prolog.cpp
	../src/print_souffle.cpp
	../src/proof.cpp
	../src/save_csv.cpp
	../src/tables.cpp
	../src/tables.h
	../src/transform.cpp
)

set(JSLIB_COMPILE_OPTIONS
	"$<$<CONFIG:DEBUG>:-O0;-DDEBUG;-g4>"
	"$<$<CONFIG:RELEASE>:-O3;-DNDEBUG;-g0>"
)
set(JSLIB_LINK_OPTIONS "--bind")
string(APPEND JSLIB_LINK_OPTIONS " -s WASM=1")
string(APPEND JSLIB_LINK_OPTIONS " -s ALLOW_MEMORY_GROWTH=1")
string(APPEND JSLIB_LINK_OPTIONS " -s ASSERTIONS=1")
string(APPEND JSLIB_LINK_OPTIONS " -s EXIT_RUNTIME=1")
string(APPEND JSLIB_LINK_OPTIONS " -s WARN_UNALIGNED=1")
string(APPEND JSLIB_LINK_OPTIONS " -s MODULARIZE_INSTANCE=1")
string(APPEND JSLIB_LINK_OPTIONS " -s EXPORT_NAME='tml'")
string(APPEND JSLIB_LINK_OPTIONS " -s DISABLE_EXCEPTION_CATCHING=0")

# tml.js library
add_executable(tml)
target_setup(tml)
target_compile_options(tml PRIVATE ${JSLIB_COMPILE_OPTIONS})
set_target_properties(tml PROPERTIES LINK_FLAGS ${JSLIB_LINK_OPTIONS})
target_sources(tml PRIVATE ${JSLIB_SOURCES})
