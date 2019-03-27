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

bool lp::add_fact(size_t f, int_t rel, ints arity) {
	size_t *t = db[{rel, arity}];
	*t = bdd_or(*t, f);
	t = ndb[{rel, arity}];
	return F != (*t = bdd_and_not(*t, f));
}

bool lp::add_not_fact(size_t f, int_t rel, ints arity) {
	size_t *t = ndb[{rel, arity}];
	*t = bdd_or(*t, f);
	t = db[{rel, arity}];
	return F != (*t = bdd_and_not(*t, f));
}

bool lp::add_fact(const term& x) {
	if (x.neg) return add_not_fact(fact(x, bits), x.rel, x.arity);
	return add_fact(fact(x, bits), x.rel, x.arity);
}

lp::lp(matrices r, matrix g, matrix pg, size_t dsz, lp *prev)
	: pgoals(move(pg)), prev(prev), dsz(dsz) {
	//wcout<<r<<endl;
/*	dsz = 0;
	for (const matrix& m : r)
		for (const term& t : m) 
			for (int_t i : t) if (i > 0) dsz = max(dsz, (size_t)i);
	dsz = max(prev?prev->dsz:dsz+1, dsz+1);
	for (const term& t : g)
		if (t.size()-1 > ar) er(err_goalarity);
		else for (int_t i:t) if (i > 0 && i>=(int_t)dsz)er(err_goalsym);
	for (const term& t : pgoals)
		if (t.size()-1 > ar) er(err_goalarity);
		else for (int_t i : t)
			if (i > 0 && i>=(int_t)dsz) er(err_goalsym);
	rules_pad(r), rule_pad(g), rule_pad(pgoals),*/
	bits = msb(dsz);
	for (const matrix& m : r)
		for (const term& t : m) {
			*(db[{t.rel, t.arity}] = new size_t) = F;
			size_t *x = ndb[{t.rel, t.arity}] = new size_t;
			*x = T;
			for (size_t n = 0; n < t.args.size(); ++n)
				from_range(dsz, bits, bits * n, *x);
		}
	for (const matrix& m : r)
 		if (m.size() == 1) {
			if (!add_fact(m[0]))
				(wcout << L"contradictory fact: "<<m[0]<<endl),
				exit(0);
		} else {
			vector<size_t*> dbs;
			for (size_t n = 1; n < m.size(); ++n)
				dbs.push_back((m[n].neg?ndb:db)
					[{m[n].rel,m[n].arity}]);
			rules.emplace_back(
				new rule(m, dbs, bits, dsz, !pgoals.empty()));
		}
	DBG(printdb(wcout<<L"pos:"<<endl, this));
	DBG(printndb(wcout<<L"neg:"<<endl, this))<<endl;
/*	if (!pgoals.empty())
		proof1 = new lp(move(get_proof1()), matrix(), matrix(), dsz, this),
		proof2 = new lp(move(get_proof2()), matrix(), matrix(), dsz, proof1);*/
	for (const term& t : g) gbdd = bdd_or(gbdd, fact(t, bits));
}
/*
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
*/
void lp::fwd(diff_t &add, diff_t &del) {
	DBG(printdb(wcout, this));
	for (rule* r : rules) {
//		if (add.find({r->hrel, r->harity}) == add.end())
//			add[{r->hrel, r->harity}] = del[{r->hrel, r->harity}]=F;
		(r->neg ? del : add)[{r->hrel, r->harity}] = bdd_or(r->fwd(bits)
				,(r->neg?del:add)[{r->hrel, r->harity}]);
	}
//	DBG(printbdd(wcout<<"add:"<<endl,this,add););
//	DBG(printbdd(wcout<<"del:"<<endl,this,del););
}
/*
size_t align(size_t x, size_t par, size_t pbits, size_t ar, size_t bits) {
	return bdd_pad(bdd_rebit(x, pbits, bits, ar*bits), par, ar, pad, bits);
}*/

struct diffcmp {
	bool operator()(const lp::diff_t& x, const lp::diff_t& y) const {
		if (x.size() != y.size()) return x.size() < y.size();
		auto xt = x.begin(), yt = y.begin();
		while (xt != x.end())
			if (xt->first != yt->first)
				return xt->first < yt->first;
			else if (xt->second != yt->second)
				return xt->second < yt->second;
			else ++xt, ++yt;
		return false;
	}
};

lp::diff_t copy(const lp::db_t& x) {
	lp::diff_t r;
	for (auto y : x) r[y.first] = *y.second;
	return r;
}

bool bdd_and_not(const lp::diff_t& x, const lp::diff_t& y, lp::diff_t& r) {
	for (auto t : x) {
		auto it = y.find(t.first);
		if (it == y.end()) continue;
		if (t.second && F == (r[t.first] 
				= bdd_and_not(t.second, y.at(t.first))))
			return false;
	}
	return true;
}

lp::db_t& bdd_and_not(lp::db_t& x, const lp::diff_t& y) {
	for (auto t : x) {
		auto it = y.find(t.first);
		if (it == y.end()) continue;
		*t.second = bdd_and_not(*t.second, y.at(t.first));
	}
	return x;
}

void bdd_or(lp::db_t& x, const lp::diff_t& y) {
	for (auto t : x) {
		auto it = y.find(t.first);
		if (it == y.end()) continue;
		*t.second = bdd_or(*t.second, y.at(t.first));
	}
}

bool operator==(const lp::db_t& x, const lp::diff_t& y) {
	if (x.size() != y.size()) return false;
	auto xt = x.begin();
	auto yt = y.begin();
	while (xt != x.end())
		if (xt->first != yt->first || *xt->second != yt->second)
			return false;
		else ++xt, ++yt;
	return true;
}

bool lp::pfp() {
//	DBG(wcout<<"next prog"<<endl;)
	if (prev) {
		if (!prev->pfp()) return false;
		for (auto x : prev->db)
			if (db.find(x.first) != db.end())
				*db[x.first] = bdd_or(*db[x.first], *x.second);
			else *(db[x.first] = new size_t) = *x.second;
		for (auto x : prev->ndb)
			if (ndb.find(x.first) != ndb.end())
				*ndb[x.first] = bdd_or(*ndb[x.first],*x.second);
			else *(ndb[x.first] = new size_t) = *x.second;
//		db = bdd_or(db, align(prev->db, prev->ar, prev->bits, ar,bits));
	}
	diff_t d, add, del, t;
	set<size_t> pf;
//	wcout << V.size() << endl;
	for (set<diff_t, diffcmp> s;;) {
		s.emplace(d = copy(db)), fwd(add, del);
		for (auto x : add)
			if (!add_fact(x.second, x.first.first, x.first.second))
				return false;
		for (auto x : del)
			if(!add_not_fact(x.second,x.first.first,x.first.second))
				return false;
//		if (!bdd_and_not(add, del, t))
//			return false; // detect contradiction
//		else bdd_or(bdd_and_not(db, del), t);
		if (db == d) break;
		if (s.find(copy(db)) != s.end()) return false;
	}
//	DBG(drv->printdb(wcout<<"after: "<<endl, this)<<endl;)
//	if (proof1) return db=prove(), ar=proof2->ar, bits = proof2->bits, true;
//	if (gbdd != F) db = bdd_and(gbdd, db);
	return true;
}

size_t lp::prove() const {
	return F;
/*	size_t add, del;
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
		proof2->bits), bdd_and_not(proof2->db, get_sym_bdd(openp, 0)));*/
}
/*
size_t lp::get_varbdd(size_t par) const {
	size_t t = F;
	for (const rule* r : rules) t = bdd_or(r->get_varbdd(bits, par), t);
	return t;
}
*/
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
	os << t.rel << ' ';
	for (auto x : t.args) os << x << ' ';
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
