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

#define err_goalsym "goal symbol not appearing in program.\n"
#define err_goalarity "goal arity larger than the program's.\n"

void tml_init() { bdd_init(); }
wostream& operator<<(wostream& os, const bools& x);
wostream& operator<<(wostream& os, const vbools& x);
wostream& operator<<(wostream& os, const matrix& m);
DBG(wostream& printbdd(wostream& os, size_t t);)

size_t fact(term v, size_t bits) {
	size_t r = T;
	map<int_t, size_t> m;
	auto it = m.end();
	for (size_t j = 0; j != v.size() - 1; ++j)
		if (v[j+1] >= 0) from_int_and(v[j+1], bits, j * bits, r);
		else if (m.end() == (it = m.find(v[j+1]))) m.emplace(v[j+1],j);
		else for (size_t b = 0; b!=bits; ++b)
			r = bdd_and(r, from_eq(j*bits+b, it->second*bits+b));
	return v[0] < 0 ? bdd_and_not(T, r) : r;
}

lp::lp(matrices r, matrix g, matrices pg, lp *prev) 
	: pgoals(move(pg)), prev(prev) {
	if (prev) ar = prev->ar, dsz = prev->dsz;
	else ar = dsz = 0;
	for (const matrix& m : r)
		for (const term& t : m) {
			ar = max(ar, t.size() - 1);
			for (int_t i : t)
				if (i > 0) dsz = max(dsz, (size_t)i);
		}
	for (const term& t : g)
		if (t.size()-1 > ar) er(err_goalarity);
		else for (int_t i:t) if (i > 0 && i>=(int_t)dsz)er(err_goalsym);
	for (const matrix& m : pgoals)
		for (const term& t : m)
			if (t.size()-1 > ar) er(err_goalarity);
			else for (int_t i:t)
				if (i > 0 && i>=(int_t)dsz) er(err_goalsym);
	rules_pad(r), rule_pad(g), rules_pad(pgoals), bits = msb(dsz);
	for (const matrix& m : r)
 		if (m.size() == 1) db = bdd_or(db, fact(m[0], bits));
		else rules.emplace_back(new rule(m, bits, dsz,!pgoals.empty()));
	if (!pgoals.empty())
		proof1 = new lp(get_proof1(), matrix(), matrices()),
		proof2 = new lp(get_proof2(), matrix(), matrices()),
		proof3 = new lp(get_proof3(), matrix(), matrices());
	for (const term& t : g) gbdd = bdd_or(gbdd, fact(t, bits));
}

size_t lp::prove() const {
	size_t add, del;
	if (!proof1) return gbdd == F ? db : bdd_and(gbdd, db);
	proof1->db = get_varbdd(proof1->ar);
	proof1->fwd(proof2->db, del);
	assert(del == F);
	assert(proof2->pfp());
	proof3->db = proof2->db;
	assert(proof3->pfp());
	return bdd_or(bdd_pad(bdd_and(gbdd, db), ar, proof3->ar, pad, bits),
		proof3->db);
}

matrices lp::get_proof1() const {
	matrices p;
	for (const rule* r : rules) p.emplace(r->proof1);
	return p;
}

matrices lp::get_proof2() const {
	matrices p;
	for (const rule* r : rules) p.insert(r->proof2.begin(),r->proof2.end());
	return p;
}

matrices lp::get_proof3() const {
	matrices p;
	for (const rule* r : rules) p.insert(r->proof3.begin(),r->proof3.end());
	return p;
}

void lp::term_pad(term& t) {
	size_t l;
	if ((l=t.size())<ar+1) t.resize(ar+1), fill(t.begin()+l, t.end(), pad);
}

void lp::rule_pad(matrix& t) { for (term& x : t) term_pad(x); }

matrix lp::rule_pad(const matrix& t) {
	matrix r;
	rule_pad(r = t);
	return r;
}

void lp::rules_pad(matrices& t) {
	matrices r = move(t);
	t.clear();
	for (const matrix& x : r) t.emplace(rule_pad(x));
}

void lp::fwd(size_t &add, size_t &del) {
	cache.pos.clear(), cache.neg.clear();
	for (rule* r : rules)
		(r->neg ?del : add) =
			bdd_or(r->fwd(db,bits,ar,cache),r->neg?del:add);
}

bool lp::pfp() {
	if (prev) {
		if (!prev->pfp()) return false;
		db = prev->db;
	}
	size_t d, add, del, t;
	set<size_t> pf;
//	wcout << V.size() << endl;
	for (set<int_t> s;;) {
		add =del = F, s.emplace(d = db), fwd(add, del);
		if ((t = bdd_and_not(add, del)) == F && add != F)
			return false; // detect contradiction
		else db = bdd_or(bdd_and_not(db, del), t);
		if (d == db) break;
		if (s.find(db) != s.end()) return false;
	}
	db = prove();
	return true;
}

size_t lp::get_varbdd(size_t par) const {
	size_t t = F;
	for (const rule* r : rules) t = bdd_or(r->get_varbdd(bits, par), t);
	return t;
}

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

size_t lp::maxw() const {
	size_t r = 0;
	for (const rule* x : rules) r = max(r, x->bd.size());
	return r;
}

matrix lp::getdb() const { return getbdd(db); }
matrix lp::getbdd(size_t t) const { return getbdd(t, bits, ar); }
matrix lp::getbdd_one(size_t t) const { return getbdd_one(t, bits, ar); }
matrix lp::getbdd(size_t t, size_t b, size_t a) const{return from_bits(t,b,a);}
matrix lp::getbdd_one(size_t t, size_t b, size_t a) const {
	return {one_from_bits(t,b,a)};
}
lp::~lp() {
	for (rule* r : rules) delete r;
	if (prev) delete prev;
	if (proof1) delete proof1, delete proof2, delete proof3;
}

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
