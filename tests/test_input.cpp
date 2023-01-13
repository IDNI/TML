
#include "unittest.hpp"
#include <iostream>
#include <string>
#include <vector>
#include "../src/input.h"

using namespace idni;

TEST_SUITE("input processing test") {
	TEST_CASE("string input") {
		ccs s = to_string_t("string").c_str();
		input i(s);
		CHECK(i.begin() == i.data());
	}
	TEST_CASE("file input") {
		input i(std::string("./input.test.file"));
		EXPECT_FALSE(i.error);
		CHECK(i.begin() == i.data());
	}
	TEST_CASE("multiple inputs") {
		inputs ii;
		std::string
			prog1 = "a. b :- a.",
			prog2 = "c. d :- a, b, c.",
			prog3 = "a.\nb.\nc :- a, b.\n";
		CHECK(ii.size() == 0);
		ii.add_string(prog1);
		CHECK(ii.size() == 1);
		ii.add_string(prog2);
		CHECK(ii.size() == 2);
		ii.add_file("./input.test.file");
		EXPECT_FALSE(ii.last()->error);
		CHECK(ii.size() == 3);

		input* i = ii.first();
		CHECK(i != 0);
		CHECK(string_t(i->data())  == to_string_t(prog1));
		CHECK(string_t(i->begin()) == to_string_t(prog1));
	
		i = i->next();
		CHECK(i != 0);
		CHECK(string_t(i->data())  == to_string_t(prog2));
		CHECK(string_t(i->begin()) == to_string_t(prog2));
	
		i = i->next();
		CHECK(i != 0);
		CHECK(string_t(i->data())  == to_string_t(prog3));
		CHECK(string_t(i->begin()) == to_string_t(prog3));

		CHECK(i->next() == 0);		
	}
    	TEST_CASE("tokenizing input string") {
        	string_t emptyString = to_string_t("                                   ");
        	input in1(emptyString.c_str());
        	CHECK(in1.l.size() == 0);
        	string_t stringWithComment = to_string_t(" /*  ");
		input in2(stringWithComment.c_str());
		CHECK((in2.prog_lex(), in2.error == true));
		string_t s = to_string_t(
			"setB(?x ?y ?z) :- e(?x), e(?y), ?x + ?y = ?z. ?x > ?y.");
		input in3(s.c_str());
		in3.prog_lex();
		CHECK(in3.l.size() == 27);
	}
}

