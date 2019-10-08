set(EMSCRIPTEN_CMAKE "${EMSCRIPTEN_DIR}/cmake/Modules/Platform/Emscripten.cmake")

# checks if emscripten toolchain file is available
function(emscripten_toolchain_available AVAILABLE)
	if(EXISTS "${EMSCRIPTEN_CMAKE}")
		set(${AVAILABLE} TRUE PARENT_SCOPE)
	else()
		set(${AVAILABLE} FALSE PARENT_SCOPE)
	endif()
endfunction()

# sets emscripten toolchain file if available
function(set_emscripten_toolchain)
	emscripten_toolchain_available(EMSCRIPTEN_TOOLCHAIN_AVAILABLE)
	if (NOT ${EMSCRIPTEN_TOOLCHAIN_AVAILABLE})
		message(SEND_ERROR "emscripten not found in ${EMSCRIPTEN_DIR}. Use -DEMSCRIPTEN_DIR=<emscripten_install_directory>.")
	else()
		set(EMSCRIPTEN_ROOT_PATH "${EMSCRIPTEN_DIR}")
		set(CMAKE_TOOLCHAIN_FILE
			"${EMSCRIPTEN_DIR}/cmake/Modules/Platform/Emscripten.cmake"
			PARENT_SCOPE)
	endif()
endfunction()
