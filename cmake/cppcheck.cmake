find_program(CPPCHECK cppcheck)
if (CPPCHECK)
    message(STATUS "Found cppcheck")
    set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
    add_custom_target(cppcheck COMMAND
            ${CPPCHECK}
            --suppress=syntaxError
            --enable=all
            --inconclusive
            -j ${CORE_COUNT}
            --project=${CMAKE_BINARY_DIR}/compile_commands.json
            --quiet
            --std=c++17
            -DBOOST_AUTO_TEST_SUITE
            -DTOOLBOX_BENCHMARK
            -DTOOLBOX_BENCHMARK_MAIN
            )
else ()
    message(WARNING "Cppcheck not found!")
endif ()
