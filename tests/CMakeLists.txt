set(DOCTEST_CONFIG_ASSERTION_PARAMETERS_BY_VALUE "true")

add_link_options("-flto")

set(TML_TESTS test_input.cpp)
add_executable(test_input ${TML_TESTS})
target_setup(test_input)
target_link_libraries(test_input TMLo ${TEST_FRAMEWORK})

set(TEST_OUTPUT test_output.cpp)
add_executable(test_output ${TEST_OUTPUT})
target_setup(test_output)
target_link_libraries(test_output TMLo ${TEST_FRAMEWORK})

set(TEST_ITERATORS test_iterators.cpp)
add_executable(test_iterators ${TEST_ITERATORS})
target_setup(test_iterators)
target_link_libraries(test_iterators TMLo ${TEST_FRAMEWORK})

set(TEST_TRANSFORM_OPT test_transform_opt.cpp)
add_executable(test_transform_opt ${TEST_TRANSFORM_OPT})
target_setup(test_transform_opt)
target_link_libraries(test_transform_opt TMLo ${TEST_FRAMEWORK})

set(TEST_EARLEY test_earley.cpp)
add_executable(test_earley ${TEST_EARLEY})
target_setup(test_earley)
target_link_libraries(test_earley TMLo ${TEST_FRAMEWORK})

add_custom_target(tmltest
	COMMAND test_input && tml_output && tml_earley && test_iterators && test_transform_opt
	DEPENDS test_input test_output test_earley test_iterators test_transform_opt)

# add_test(NAME test_input COMMAND "${PROJECT_BINARY_DIR}/test_input")
add_test(NAME test_output COMMAND "${PROJECT_BINARY_DIR}/test_output")
add_test(NAME test_iterators COMMAND "${PROJECT_BINARY_DIR}/test_iterators")
# add_test(NAME test_transform_opt COMMAND "${PROJECT_BINARY_DIR}/test_transform_opt")
add_test(NAME test_earley COMMAND "${PROJECT_BINARY_DIR}/test_earley")

find_program (BASH_PROGRAM bash)
if (BASH_PROGRAM)
  add_test (regression ${BASH_PROGRAM} ${CMAKE_CURRENT_SOURCE_DIR}/tests/run_all_regression_tests.sh)
endif (BASH_PROGRAM)