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
DBG(wostream& printbdd(wostream& os, size_t t);)

lp::lp(matrices r, matrix g, matrix pg, lp *prev) : pgoals(move(pg)),prev(prev){
	//wcout<<r<<endl;
	dsz = 0;
	if (prev) ar = prev->ar;
	else ar = 0;
	for (const matrix& m : r)
		for (const term& t : m) {
			ar = max(ar, t.size() - 1);
			for (int_t i : t) if (i > 0) dsz = max(dsz, (size_t)i);
		}
	dsz = max(prev?prev->dsz:dsz+1, dsz+1);
	for (const term& t : g)
		if (t.size()-1 > ar) er(err_goalarity);
		else for (int_t i:t) if (i > 0 && i>=(int_t)dsz)er(err_goalsym);
	for (const term& t : pgoals)
		if (t.size()-1 > ar) er(err_goalarity);
		else for (int_t i : t)
			if (i > 0 && i>=(int_t)dsz) er(err_goalsym);
	rules_pad(r), rule_pad(g), rule_pad(pgoals), bits = msb(dsz);
	for (const matrix& m : r)
 		if (m.size() == 1) db = bdd_or(db, fact(m[0], bits));
		else rules.emplace_back(new rule(m, bits, dsz,!pgoals.empty()));
	if (!pgoals.empty())
		proof1 = new lp(move(get_proof1()), matrix(), matrix(), this),
		proof2 = new lp(move(get_proof2()), matrix(), matrix(), proof1);
	for (const term& t : g) gbdd = bdd_or(gbdd, fact(t, bits));
}

matrices lp::get_proof1() const {
	matrices p;
	for (const rule* r : rules) p.emplace(r->proof1);
	return p;
}

matrices lp::get_proof2() const {
	matrices p;
	matrix m;
	for (const rule* r : rules) p.insert(r->proof2.begin(),r->proof2.end());
	for (const term& t : pgoals)
		m.resize(1), m[0] = { 1, openp },
		m[0].insert(m[0].begin()+2, t.begin()+1, t.end()), 
		m[0].push_back(closep), p.insert(move(m));
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
//	DBG(printbdd(wcout<<"add:"<<endl,this,add););
//	DBG(printbdd(wcout<<"del:"<<endl,this,del););
}

size_t align(size_t x, size_t par, size_t pbits, size_t ar, size_t bits) {
	return bdd_pad(bdd_rebit(x, pbits, bits, ar*bits), par, ar, pad, bits);
}

bool lp::pfp() {
//	DBG(wcout<<"next prog"<<endl;)
	if (prev) {
		if (!prev->pfp()) return false;
		db = bdd_or(db, align(prev->db, prev->ar, prev->bits, ar,bits));
	}
	size_t d, add, del, t;
	set<size_t> pf;
//	wcout << V.size() << endl;
	for (set<int_t> s;;) {
		add = del = F, s.emplace(d = db), fwd(add, del);
		if ((t = bdd_and_not(add, del)) == F && add != F)
			return false; // detect contradiction
		else db = bdd_or(bdd_and_not(db, del), t);
		if (d == db) break;
		if (s.find(db) != s.end()) return false;
	}
//	DBG(drv->printdb(wcout<<"after: "<<endl, this)<<endl;)
	if (proof1) return db=prove(), ar=proof2->ar, bits = proof2->bits, true;
	if (gbdd != F) db = bdd_and(gbdd, db);
	return true;
}

size_t lp::prove() const {
	size_t add, del;
	proof1->db = get_varbdd(proof1->ar);
//	DBG(printbdd(wcout<<"p1db before:"<<endl,proof1,proof1->db)<<endl;);
	proof1->fwd(add = F, del = F);
	proof2->db = bdd_or(proof2->db, add);
//	DBG(printbdd(wcout<<"add:"<<endl,proof1,proof1->db)<<endl;);
//	DBG(printbdd(wcout<<"p2db before:"<<endl,proof2,proof2->db)<<endl;);
	proof2->prev = 0;
	assert(del == F);
	assert(proof2->pfp());
//	DBG(printbdd(wcout<<"p2db after:"<<endl,proof2,proof2->db)<<endl;);
	if (gbdd == F) return bdd_and_not(proof2->db, get_sym_bdd(openp, 0));
	return bdd_or(align(bdd_and(gbdd, db), ar, bits, proof2->ar,
		proof2->bits), bdd_and_not(proof2->db, get_sym_bdd(openp, 0)));
}

size_t lp::get_varbdd(size_t par) const {
	size_t t = F;
	for (const rule* r : rules) t = bdd_or(r->get_varbdd(bits, par), t);
	return t;
}

size_t lp::get_sym_bdd(size_t sym, size_t pos) const {
	return from_int(sym, bits, bits * pos);
}
/*
size_t lp::maxw() const {
	size_t r = 0;
	for (const rule* x : rules) r = max(r, x->bd.size());
	return r;
}
*/
matrix lp::getdb() const { return getbdd(db); }
matrix lp::getbdd(size_t t) const { return from_bits(t,bits,ar); }
matrix lp::getbdd_one(size_t t) const { return {one_from_bits(t,bits,ar)}; }
lp::~lp() {
//	for (rule* r : rules) delete r;
//	if (prev) delete prev;
//	if (proof1) delete proof1, delete proof2;
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
wostream& operator<<(wostream& os, const term& t) {
	for (auto x : t) os << x << ' ';
	return os;
}
wostream& operator<<(wostream& os, const matrix& m) {
	for (const term& t : m) os << t << ',';
	return os;
}
wostream& operator<<(wostream& os, const matrices& m) {
	for (const matrix& x : m) os << x << endl;
	return os;
}
