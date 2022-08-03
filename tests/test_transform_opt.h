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
#ifndef __TEST_TRANSFORM_H__
#define __TEST_TRANSFORM_H__

#include "unittest.hpp"
#include "../src/transform_opt.h"

#ifndef WORK_IN_PROGRESS

/* Factory methods to easy test cases building */
term term_f(std::vector<int_t> args) {
	term t;	for (auto a: args ) t.emplace_back(a); return t;
}

std::vector<term> rule_f(std::vector<term> terms) {
	std::vector<term> r; for (auto t: terms) r.emplace_back(t); return r;
}

flat_prog flat_prog_f(std::vector<std::vector<term>> terms) {
	flat_prog fp; for (auto t: terms) fp.insert(t);	return fp;
}

int_t sym_f() {	static int_t s = 0; return ++s; }
int_t sym_f(int_t s) {	return s; }
int_t var_f() { static int_t v = 0; return --v; }
int_t var_f(int_t v) {	return v; }

#endif // WORK_IN_PROGRESS
#endif // __TEST_TRANSFORM_H__