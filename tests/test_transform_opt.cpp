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
	TEST_CASE("squaring empty flat program returns an empty flat program") { 
		flat_prog fp;
		EXPECT_TRUE( square_program(fp).empty() ); 
	}
	TEST_CASE("squaring a single fact with no arguments") {
		auto fp = flat_prog_f({{{'a'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 // only one rule
			&& rules_e(sqr)[0] == rule_f({{'a'}})); 
	}
	TEST_CASE("squaring a single fact with one argument") { 
		auto fp = flat_prog_f({{{'a', '1'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 // only one rule
			&& rules_e(sqr)[0] == rule_f({{'a', '1'}}));
	}
	TEST_CASE("squaring a single fact with several arguments") { 
		auto fp = flat_prog_f({{{'a', '1', '2'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 // only one rule
			&& rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}));
	}
	TEST_CASE("squaring multiple unrelated facts") { 
		auto fp = flat_prog_f({
			{{'a', '1'}}, 
			{{'b', '1'}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 2 // only two rules
			&& rules_e(sqr)[0] == rule_f({{'a', '1'}}) 
			&& rules_e(sqr)[1] == rule_f({{'b', '1'}}));
	 }
	TEST_CASE("squaring a rule and a fact") { 
		auto x1 = var_f();
		auto fp = flat_prog_f({
			{{'a', '1'}},
			{{'b', x1}, /* :- */ {'a', x1}}});
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 2 // only two rules
			&& rules_e(sqr)[0] == rule_f({{'a', '1'}})
			&& rules_e(sqr)[1] == rule_f({{'b', '1'}}));
	}
	TEST_CASE("squaring a single rule") { EXPECT_TRUE(false); }
	TEST_CASE("squaring two unrelated rules") { EXPECT_TRUE(false); }
	TEST_CASE("squaring two related rules") { EXPECT_TRUE(false); }
}

#endif // WORK_IN_PROGRESS
