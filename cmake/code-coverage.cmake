include(CodeCoverage)

message(STATUS "Setting up code coverage")

set(COVERAGE_LCOV_EXCLUDES
        '${CMAKE_SOURCE_DIR}/build-*/*'
        '${CMAKE_SOURCE_DIR}/cmake-build-debug/*'
        )
set(COVERAGE_GCOVR_EXCLUDES ${COVERAGE_LCOV_EXCLUDES})

setup_target_for_coverage_gcovr_xml(
        NAME doctest_coverage
        EXECUTABLE ${CMAKE_SOURCE_DIR}/build-Debug/tests/test_tml
)

setup_target_for_coverage_gcovr_html(
        NAME doctest_coverage_html
        EXECUTABLE ${CMAKE_SOURCE_DIR}/build-Debug/tests/test_tml
)
