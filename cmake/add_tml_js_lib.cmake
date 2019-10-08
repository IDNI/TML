set(TML_JS_FILES
	"${CMAKE_CURRENT_BINARY_DIR}/tml.js"
	"${CMAKE_CURRENT_BINARY_DIR}/tml.wasm")

# adds tml_js_lib target
function(add_tml_js_lib)
	set(TML_JS_BUILD_DIR
		"${PROJECT_SOURCE_DIR}/build-tml.js-${CMAKE_BUILD_TYPE}")
	add_custom_command(OUTPUT ${TML_JS_BUILD_DIR}
		COMMAND mkdir -p ${TML_JS_BUILD_DIR}
		COMMENT "creating build directory for tml_js_lib"
		VERBATIM
	)
	add_custom_target(tml_js_lib_build_dir DEPENDS ${TML_JS_BUILD_DIR})
	add_custom_command(OUTPUT ${TML_JS_FILES}
		COMMAND ${CMAKE_COMMAND} --output-debug ${TML_DIR} -DBUILD_JSLIB=on -DEMSCRIPTEN_DIR=${EMSCRIPTEN_DIR}
			&& ${CMAKE_COMMAND} --build .
			&& cp ${TML_JS_BUILD_DIR}/tml.js ${TML_JS_BUILD_DIR}/tml.wasm ${CMAKE_CURRENT_BINARY_DIR}
		WORKING_DIRECTORY ${TML_JS_BUILD_DIR}
		COMMENT "added tml_js_lib target"
		VERBATIM
	)
	add_custom_target(tml_js_lib DEPENDS tml_js_lib_build_dir ${TML_JS_FILES})
endfunction()
