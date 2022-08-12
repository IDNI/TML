// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.
#include "test_transform_opt.h"

#ifndef WORK_IN_PROGRESS

TEST_SUITE("transform_opt-squaring") {
	TEST_CASE("squaring: .") { 
		flat_prog fp;
		EXPECT_TRUE( square_program(fp).empty() ); 
	}
	TEST_CASE("squaring: a.") {
		auto fp = flat_prog_f({{{'a'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1);
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a'}})); 
	}
	TEST_CASE("squaring: a(1).") { 
		auto fp = flat_prog_f({{{'a', '1'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1);
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1'}}));
	}
	TEST_CASE("squaring: a(1 2).") { 
		auto fp = flat_prog_f({{{'a', '1', '2'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1);
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}));
	}
	TEST_CASE("squaring: a(1). b(1).") { 
		auto fp = flat_prog_f({
			{{'a', '1'}}, 
			{{'b', '1'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1'}}) ); 
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', '1'}}) );
	}
	TEST_CASE("squaring: a(?x).") { 
		auto x = var_f();
		auto fp = flat_prog_f({{{'a', x}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', x}}) ); 
	}
	TEST_CASE("squaring: a(1). b(x?):-a(x?).") { 
		auto x = var_f();
		auto fp = flat_prog_f({
			{{'a', '1'}},
			{{'b', x}, /* :- */ {'a', x}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', '1'}}) );
	}
	TEST_CASE("squaring: a(1 2). b(?x):-a(x? y?). c(?x):-a(y? x?).") { 
		auto x = var_f(); auto y = var_f();
		auto fp = flat_prog_f({
			{{'a', '1', '2'}},
			{{'b', x}, /* :- */ {'a', x, y}},
			{{'c', x}, /* :- */ {'a', y, x}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 3 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', '1'}}) );
		EXPECT_TRUE( rules_e(sqr)[2] == rule_f({{'c', '2'}}) );
	}
	TEST_CASE("squaring: a(1 2). b(?x):-a(x? x?).") { 
		auto x = var_f(); 
		auto fp = flat_prog_f({
			{{'a', '1', '2'}},
			{{'b', x}, /* :- */ {'a', x, x}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 2 ); 
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', x},{'a', x, x}}) );
	}
	TEST_CASE("squaring: a(1 2). b(?x):-a(2 x?).") { 
		auto x = var_f(); 
		auto fp = flat_prog_f({
			{{'a', '1', '2'}},
			{{'b', x}, /* :- */ {'a', '2', x}}});
		auto sqr = square_program(fp); 

		#ifndef DELETE_ME
		std::cout << "SQR PROGRAM:"<< std::endl;
		for (auto r: sqr) {
			std::cout << "RULE: {";
			for (auto t: r) {
				for (auto i: t) {
				std::cout << i << ",";
				}
			}
			std::cout << "}" << std::endl;
		}
		#endif // DELETE_ME

		EXPECT_TRUE( sqr.size() == 2 ); 
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', x}, {'a', '2', x}}) );
	}
}

TEST_SUITE("transform_opt-splitting") {
	TEST_CASE("splitting: .") { 
		EXPECT_TRUE( true ); 
	}
	TEST_CASE("splitting: a(1).") { 
		EXPECT_TRUE( true ); 
	}
	TEST_CASE("splitting: a(?x):-b(?x).") { 
		EXPECT_TRUE( true ); 
	}
	TEST_CASE("splitting: a(?x):-b(?x), c(?x).") { 
		EXPECT_TRUE( true ); 
	}
	TEST_CASE("splitting: a(?x):-b(?x ?y), c(?x ?y).") { 
		EXPECT_TRUE( true ); 
	}
}

TEST_SUITE("query containment") {
}

TEST_SUITE("minimization") {
}
#endif // WORK_IN_PROGRESS
