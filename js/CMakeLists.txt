# This lists file requires CMAKE_TOOLCHAIN_FILE to be set
# to "<EMSCRIPTEN_DIR>/cmake/Modules/Platform/Emscripten.cmake"
# or use emscripten_toolchain module from ../cmake
# This setting must be done before using project()

cmake_minimum_required(VERSION 3.13)

project(tml)

option(WITH_THREADS "use Threads" FALSE)

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(tml-common)

set(JSLIB_SOURCES
	../src/bdd.cpp
	../src/bdd.h
	../src/bdd_arith.cpp
	../src/builtins.cpp
	../src/builtins.h
	../src/char_defs.h
	../src/cpp_gen.cpp
	../src/cpp_gen.h
	../src/defs.h
	../src/dict.cpp
	../src/dict.h
	../src/driver.cpp
	../src/driver.h
	../src/earley.cpp
	../src/earley.h
	../src/err.h
	../src/form.cpp
	../src/form.h
	../src/input.cpp
	../src/input.h
	../src/ir_builder.cpp
	../src/ir_builder.h
	../src/memory_map.h
	../src/options.cpp
	../src/options.h
	../src/output.cpp
	../src/output.h
	../src/printing.cpp
	../src/printing.h
	../src/proof.cpp
	../src/save_csv.cpp
	../src/tables.cpp
	../src/tables.h
	../src/tables_builtins.cpp
	../src/tables_ext.cpp
	../src/term.h
	../src/tml_earley.cpp
	../src/transform.cpp
	../src/transform_bitunv.cpp
	../src/transform_guards.cpp
	../src/typemanager.cpp
	../src/typemanager.h
	../src/utils.cpp
)

set(JSLIB_COMPILE_OPTIONS
	"$<$<CONFIG:DEBUG>:-O0;-DDEBUG;-gsource-map;-fno-exceptions>"
	"$<$<CONFIG:RELEASE>:-O3;-DNDEBUG;-g0;-fno-exceptions>"
)
set(JSLIB_LINK_OPTIONS "--bind --no-entry -lnodefs.js")
string(APPEND JSLIB_LINK_OPTIONS " -s EXPORT_NAME='tml'")
string(APPEND JSLIB_LINK_OPTIONS " -s MODULARIZE=1")
string(APPEND JSLIB_LINK_OPTIONS " -s USE_ES6_IMPORT_META=0")
string(APPEND JSLIB_LINK_OPTIONS " -s STRICT=1")
string(APPEND JSLIB_LINK_OPTIONS " -s WASM=1")
string(APPEND JSLIB_LINK_OPTIONS " -s ALLOW_MEMORY_GROWTH=1")
string(APPEND JSLIB_LINK_OPTIONS " -s EXIT_RUNTIME=1")
string(APPEND JSLIB_LINK_OPTIONS " -s ERROR_ON_UNDEFINED_SYMBOLS=1")
string(APPEND JSLIB_LINK_OPTIONS " -s DISABLE_EXCEPTION_THROWING=1")
string(APPEND JSLIB_LINK_OPTIONS " -s DISABLE_EXCEPTION_CATCHING=1")
string(APPEND JSLIB_LINK_OPTIONS " -s 'EXPORTED_RUNTIME_METHODS=[\"lengthBytesUTF8\",\"stringToUTF8\"]'")
string(APPEND JSLIB_LINK_OPTIONS " -s ASSERTIONS=1")
#string(APPEND JSLIB_LINK_OPTIONS " -s FETCH=1")
#string(APPEND JSLIB_LINK_OPTIONS " -s WARN_UNALIGNED=1")

# tmllib.js library
add_executable(tmllib)
target_setup(tmllib)
target_compile_options(tmllib PRIVATE ${JSLIB_COMPILE_OPTIONS})
set_target_properties(tmllib PROPERTIES LINK_FLAGS ${JSLIB_LINK_OPTIONS})
target_sources(tmllib PRIVATE ${JSLIB_SOURCES})	
target_compile_definitions(tmllib PRIVATE "-DNODEFSMOUNT")

# tml.js module
set(MODULE_LINK_OPTIONS ${JSLIB_LINK_OPTIONS})
string(APPEND MODULE_LINK_OPTIONS " -s EXPORT_ES6=1")
string(APPEND MODULE_LINK_OPTIONS " -s ENVIRONMENT='web,worker'")
add_executable(tml)
target_setup(tml)
target_compile_options(tml PRIVATE ${JSLIB_COMPILE_OPTIONS})
set_target_properties(tml PROPERTIES LINK_FLAGS ${MODULE_LINK_OPTIONS})
target_sources(tml PRIVATE ${JSLIB_SOURCES})
