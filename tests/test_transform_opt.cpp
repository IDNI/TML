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
		term t; auto r = rule_f({t}); auto fp = flat_prog_f({r}); 
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 // only one rule
			&& (*(sqr.begin())).size() == 1 // with only one term
			&& (*(sqr.begin()))[0] == t); //which equals t
	}
	TEST_CASE("squaring a single fact with one argument") { 
		flat_prog fp; term t; t.emplace_back(2); std::vector<term> r{t}; fp.insert(r);
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 && (*(sqr.begin()))[0] == t);
	}
	TEST_CASE("squaring a single fact with several arguments") { 
		flat_prog fp; term t; t.emplace_back(2); t.emplace_back(3); std::vector<term> r{t}; fp.insert(r);
		auto sqr = square_program(fp); 
		EXPECT_TRUE( sqr.size() == 1 && (*(sqr.begin()))[0] == t);
	}
	TEST_CASE("squaring multiple facts") { 
		flat_prog fp {
			rule_f({term_f({1,2,3}) })
		};

	 }
	TEST_CASE("squaring a rule and a fact") { EXPECT_TRUE(false); }
	TEST_CASE("squaring a single rule") { EXPECT_TRUE(false); }
	TEST_CASE("squaring two unrelated rules") { EXPECT_TRUE(false); }
	TEST_CASE("squaring two related rules") { EXPECT_TRUE(false); }
}

#endif // WORK_IN_PROGRESS
