# This lists file requires CMAKE_TOOLCHAIN_FILE to be set
# to "<EMSCRIPTEN_DIR>/cmake/Modules/Platform/Emscripten.cmake"
# or use emscripten_toolchain module from ../cmake
# This setting must be done before using project()

cmake_minimum_required(VERSION 3.13)

project(tml)

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(tml-common)

set(JSLIB_SOURCES
	../src/ast.cpp
	../src/bdd.cpp
	../src/bdd.h
	../src/defs.h
	../src/dict.h
	../src/dict.cpp
	../src/driver.cpp
	../src/driver.h
	../src/input.cpp
	../src/input.h
	../src/options.h
	../src/options.cpp
	../src/output.h
	../src/output.cpp
	../src/print_prolog.cpp
	../src/print_souffle.cpp
	../src/save_csv.cpp
	../src/tables.h
	../src/tables.cpp
	../src/transform.cpp
)

set(JSLIB_COMPILE_OPTIONS
	"$<$<CONFIG:DEBUG>:-O0;-DDEBUG;-g4>"
	"$<$<CONFIG:RELEASE>:-O3;-DNDEBUG;-g0>"
)
set(JSLIB_LINK_OPTIONS
	"--bind"
	"-s;WASM=1,EXIT_RUNTIME=1,WARN_UNALIGNED=1,MODULARIZE_INSTANCE=1,EXPORT_NAME='tml'"
)

# tml.js library
add_executable(tml)
target_setup(tml)
target_compile_options(tml PRIVATE ${JSLIB_COMPILE_OPTIONS})
target_link_options(tml PRIVATE ${JSLIB_LINK_OPTIONS})
target_sources(tml PRIVATE ${JSLIB_SOURCES})
