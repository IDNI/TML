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

/* Factory methods to ease test cases building. */
int_t sym_f() {	static int_t s = 0; return ++s; }
int_t sym_f(int_t s) {	return s < 0 ? -s: s; }
int_t var_f() { static int_t v = 0; return --v; }
int_t var_f(int_t v) {	return v > 0 ? -v : v; }

term term_f(std::vector<int_t> as) {
	term t;	
	// Add a dummy head if needed
	if (as.empty()) t.tab = sym_f();
	else t.tab = as[0], t.insert(t.end(), ++as.begin(), as.end());		
	return t;
}

std::vector<term> rule_f(std::vector<std::vector<int_t>> ts) {
	std::vector<term> r; 
	for (auto t: ts) r.emplace_back(term_f(t));
	return r;
}

flat_prog flat_prog_f(std::vector<std::vector<std::vector<int_t>>> rs) {
	flat_prog fp;
	for (auto r: rs) fp.emplace(rule_f(r));
	return fp;
}

/* Extractor methods to ease testing. */

std::vector<std::vector<term>> rules_e(flat_prog fp) {
	std::vector<std::vector<term>> v(fp.begin(), fp.end()); return v;
}

term head_e(std::vector<term> r) { return r[0]; }

std::vector<term> body_e(std::vector<term> r) {
	std::vector<term> v(++r.begin(), r.end()); return v;
}

std::vector<int_t> args_e(term t) {
	std::vector<int_t> v(++t.begin(), t.end()); return v;
}

int_t pred_e(term t) { return t[0]; }

/* Check methods to ease testing. */

bool is_var(int_t v) { return v < 0;}
bool is_sym(int_t v) { return v > 0;}

/* Helpers methods for printing intermediate results during debugging. */

std::ostream& operator<<(std::ostream &os, term &fr) {
	os << "("; for (auto p: fr) os << p; os << ")\n";
	return os;
}

std::ostream& operator<<(std::ostream &os, std::vector<term> &fr) {
	os << "{"; for (auto p: fr) os << p; os << "}\n";
	return os;
}

std::ostream& operator<<(std::ostream &os, flat_prog &fp) {
	os << "flat_prog: ["; for (auto r: fp) os << r; os << "]\n";
	return os;
}

#endif // __TEST_TRANSFORM_H__