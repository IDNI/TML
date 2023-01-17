# This CMakeLists.txt file requires CMAKE_TOOLCHAIN_FILE to be set
# to "<EMSCRIPTEN_DIR>/cmake/Modules/Platform/Emscripten.cmake"
# This setting must be done before using project()

cmake_minimum_required(VERSION 3.13)

message(STATUS "CMAKE_CXX_COMPILER_ID: ${CMAKE_CXX_COMPILER_ID}")
message(STATUS "CMAKE_CXX_COMPILER_VERSION: ${CMAKE_CXX_COMPILER_VERSION}")

option(WITH_THREADS "use Threads" FALSE)

set(WITH_ARITH TRUE CACHE BOOL "")
set(WITH_MMAP TRUE CACHE BOOL "")

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(init)

set(JSLIB_SOURCES
	../src/builtins.cpp
	../src/builtins.h
	../src/cpp_gen.cpp
	../src/cpp_gen.h
	../src/defs.h
	../src/dict.cpp
	../src/dict.h
	../src/driver.cpp
	../src/driver.h
	../src/err.h
	../src/form.cpp
	../src/form.h
	../src/input.cpp
	../src/input.h
	../src/ir_builder.cpp
	../src/ir_builder.h
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
	# BDD library
	../lib/bdd/src/bdd.cpp
	../lib/bdd/src/bdd.h
	../lib/bdd/src/bdd_arith.cpp
	../lib/bdd/src/memory_map.h
	# parser library
	../lib/parser/src/parser.cpp
	../lib/parser/src/parser.h
	../lib/parser/src/characters.cpp
	../lib/parser/src/characters.h
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

#string(APPEND JSLIB_LINK_OPTIONS " -s LINKABLE=1")
#string(APPEND JSLIB_LINK_OPTIONS " -s EXPORT_ALL=1")

#string(APPEND JSLIB_LINK_OPTIONS " -sLLD_REPORT_UNDEFINED")

# tmllib.js library
add_executable(tmllib)
target_setup(tmllib)
target_pass_features_on(tmllib)
target_compile_options(tmllib PRIVATE ${JSLIB_COMPILE_OPTIONS})
set_target_properties(tmllib PROPERTIES LINK_FLAGS ${JSLIB_LINK_OPTIONS})
target_sources(tmllib PRIVATE ${JSLIB_SOURCES})
target_compile_definitions(tmllib PRIVATE "-DNODEFSMOUNT")
target_compile_definitions(tmllib PRIVATE "-DWITH_ARITH")


# tml.js module
if(BUILD_JSMODULE)
	set(MODULE_LINK_OPTIONS ${JSLIB_LINK_OPTIONS})
	string(APPEND MODULE_LINK_OPTIONS " -s EXPORT_ES6=1")
	string(APPEND MODULE_LINK_OPTIONS " -s ENVIRONMENT='web,worker'")
	add_executable(tmljs)
	target_setup(tmljs)
	target_pass_features_on(tmljs)
	target_compile_options(tmljs PRIVATE ${JSLIB_COMPILE_OPTIONS})
	set_target_properties(tmljs PROPERTIES LINK_FLAGS ${MODULE_LINK_OPTIONS})
	target_sources(tmljs PRIVATE ${JSLIB_SOURCES})
	target_compile_definitions(tmljs PRIVATE "-DWITH_ARITH")
endif()
