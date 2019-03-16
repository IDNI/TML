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
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <cstring>
#include <iostream>
#include <random>
#include <sstream>
#include <climits>
#include <stdexcept>
#include <cassert>
#include "rule.h"
#ifdef DEBUG
#include "driver.h"
#else
#include "lp.h"
#endif
using namespace std;

void tml_init() { bdd_init(); }
wostream& operator<<(wostream& os, const bools& x);
wostream& operator<<(wostream& os, const vbools& x);
wostream& operator<<(wostream& os, const matrix& m);
DBG(wostream& printbdd(wostream& os, size_t t);)

void lp::rule_add(const matrix& x) {
 	if (x.size() == 1)
		db = bdd_or(db, rule(x, bits, dsz, matrices()).hsym);//fact
	else rules.emplace_back(new rule(x, bits, dsz, pgoals));
	lens.emplace_back();
	for (const term& t : x) lens.back().push_back(t.size() - 1);
}

void lp::goal_add(const matrix& t) {
	if (!rules.empty()) er("cannot add goals after rules");
	if (t.size() != 1) er("goals cannot have body");
	goals.emplace(t);
}

void lp::pgoal_add(const matrix& t) {
	if (!rules.empty()) er("cannot add goals after rules");
	if (t.size() != 1) er("goals cannot have body");
	pgoals.emplace(t);
}

void lp::fwd(size_t &add, size_t &del) {
	p.pos.clear(), p.neg.clear();
	for (rule* r : rules)
		(r->neg?del:add)=bdd_or(r->fwd(db,bits,ar,p),r->neg?del:add);
}
/*
size_t lp::get_varbdd() const {
	size_t t = F;
	for (const rule* r : rules)
		t = bdd_or(r->get_varbdd(bits, proof_arity()), t);
	return t;
}
*/
size_t lp::get_sym_bdd(size_t sym, size_t pos) const {
	return from_int(sym, bits, bits * pos);
}

matrix from_bits(size_t x, size_t bits, size_t ar) {
	vbools s = allsat(x, bits * ar, bits);
	matrix r(s.size());
	for (term& v : r) v = term(ar, 0);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i) {
			for (b = 0; b != bits; ++b)
				if (s[n][i * bits + b])
					r[n][i] |= 1 << (bits - b - 1);
//			if (r[n][i] == pad) break;
		}
	return r;
}

term one_from_bits(size_t x, size_t bits, size_t ar) {
	bools s(bits * ar, true);
	if (!bdd_onesat(x, bits * ar, s)) return term();
	term r(ar, 0);
	for (size_t i = 0; i != ar; ++i) {
		for (size_t b = 0; b != bits; ++b)
			if (s[i * bits + b])
				r[i] |= 1 << (bits - b - 1);
//		if (r[i] == pad) break;
	}
	return r;
}
/*
size_t lp::proof_arity() const {
	size_t r = 0;
	for (const rule* x : rules) r = max(r, x->proof_arity);
	return r;
}
*/
size_t lp::maxw() const {
	size_t r = 0;
	for (const rule* x : rules) r = max(r, x->bd.size());
	return r;
}

matrices lp::get_proof_rules() const {
	matrices r;
	for (auto x : rules) r.emplace(x->proof);
	return r;
}

matrix lp::getdb() const { return getbdd(db); }
matrix lp::getbdd(size_t t) const { return getbdd(t, bits, ar); }
matrix lp::getbdd_one(size_t t) const { return getbdd_one(t, bits, ar); }
matrix lp::getbdd(size_t t, size_t b, size_t a) const{return from_bits(t,b,a);}
matrix lp::getbdd_one(size_t t, size_t b, size_t a) const {
	return {one_from_bits(t,b,a)};
}
lp::~lp() { for (rule* r : rules) delete r; }

size_t std::hash<std::pair<size_t, bools>>::operator()(
	const std::pair<size_t, bools>& m) const {
	std::hash<size_t> h1;
	std::hash<bools> h2;
	return h1(m.first) + h2(m.second);
}

wostream& out(wostream& os,size_t n){ return out(os<<L'['<<n<<L']',getnode(n)); }
wostream& out(wostream& os, const node& n) { //print bdd in ?: syntax
	return	nleaf(n) ? os << (ntrueleaf(n) ? L'T' : L'F') :
		(out(os<<n[0]<<L'?',getnode(n[1])),out(os<<L':',getnode(n[2])));
}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x) os << (y?1:0);
	return os;
}
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) os << y << endl;
	return os;
}
wostream& operator<<(wostream& os, const matrix& m) {
	for (const term& t : m) {
		for (auto x : t) os << x << ',';
		os << endl;
	}
	return os;
}
