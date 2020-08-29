
#include "unittest.hpp"
#include <iostream>
#include <string>
#include <vector>
#include "../src/input.h"

TEST_SUITE("input processing test") {
    TEST_CASE("tokenizing input string") {
        ccs emptyString = "                                   ";
        input in1(emptyString);
        CHECK(in1.l.size() == 0);
        ccs stringWithComment = " /*  ";
	DOCTEST_CHECK_THROWS(input in2(stringWithComment));
        ccs s = "setB(?x ?y ?z) :- e(?x), e(?y), ?x + ?y = ?z. ?x > ?y.";
	input in3(s);
        CHECK(in3.l.size() == 27);
    }
}

