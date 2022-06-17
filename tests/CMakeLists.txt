set(DOCTEST_CONFIG_ASSERTION_PARAMETERS_BY_VALUE "true")

set(TML_TESTS test_input.cpp)
add_executable(test_input ${TML_TESTS})
target_setup(test_input)
target_link_libraries(test_input TMLo ${TEST_FRAMEWORK})

set(TEST_OUTPUT test_output.cpp)
add_executable(test_output ${TEST_OUTPUT})
target_setup(test_output)
target_link_libraries(test_output TMLo ${TEST_FRAMEWORK})

set(TEST_EARLEY test_earley.cpp)
add_executable(test_earley ${TEST_EARLEY})
target_setup(test_earley)
target_link_libraries(test_earley TMLo ${TEST_FRAMEWORK})

add_custom_target(tmltest
	COMMAND test_input && tml_output && tml_earley
	DEPENDS test_input test_output test_earley)
