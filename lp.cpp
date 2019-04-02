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
DBG(wostream& printbdd(wostream& os, size_t t);)

void lp::add_fact(size_t f, int_t rel, ints arity) {
	size_t *t = db[{rel, arity}];
	if (!t) *(db[{rel, arity}] = new size_t) = f;
	else *t = bdd_or(*t, f);
}

bool lp::add_not_fact(size_t f, int_t rel, ints arity) {
	size_t *t = db[{rel, arity}], p = *t;
	return (*t = bdd_and_not(*t, f)), (p == F || *t != F);
}

bool lp::add_fact(const term& x) {
//	if (x.neg) return add_not_fact(fact(x, bits, dsz), x.rel, x.arity);
	return add_fact(fact(x, bits, dsz), x.rel, x.arity), true;
}

bool lp::add_facts(const matrix& x) {
	for (auto y : x) if (!add_fact(y)) return false; // FIXME
	return true;
}

lp::lp(matpairs r, matrix g, int_t delrel, size_t dsz,
	const strs_t& strs, lp *prev) : prev(prev), bits(msb(dsz)), dsz(dsz)
	, delrel(delrel), strs(strs) {
	//wcout<<r<<endl;
/*	dsz = 0;
	for (const matrix& m : r)
		for (const term& t : m) 
			for (int_t i : t) if (i > 0) dsz = max(dsz, (size_t)i);
	dsz = max(prev?prev->dsz:dsz+1, dsz+1);
	for (const term& t : g)
		if (t.size()-1 > ar) er(err_goalarity);
		else for (int_t i:t) if (i > 0 && i>=(int_t)dsz)er(err_goalsym);
	bits = msb(dsz);*/
	for (const auto& m : r) {
		for (const term& t : m.first)
			*(db[{t.rel, t.arity}] = new size_t) = F;
		for (const term& t : m.second)
			*(db[{t.rel, t.arity}] = new size_t) = F;
	}
	for (const auto& m : r)
 		if (m.second.empty()) {
			if (!add_facts(m.first))
				// FIXME
//				(wcout << L"contradictory fact: "<<m[0]<<endl),
				exit(0);
		} else {
			vector<size_t*> dbs;
			for (size_t n = 0; n < m.second.size(); ++n)
//				if (m.second[n].b == term::NONE)
				dbs.push_back(db[{m.second[n].rel,
					m.second[n].arity}]);
			rules.emplace_back(
				new rule(m.first, m.second, dbs, bits, dsz));
		}
//	DBG(printdb(wcout<<L"pos:"<<endl, this);)
//	DBG(printndb(wcout<<L"neg:"<<endl, this)<<endl;)
	for (const term& t : g) gbdd = bdd_or(gbdd, fact(t, bits, dsz));
}

void lp::fwd(diff_t &add, diff_t &del) {
	DBG(printdb(wcout, this));
	for (rule* r : rules) {
		const sizes x = r->fwd(bits);
		if (x.empty()) continue;
		for (size_t n = 0; n != x.size(); ++n) {
			size_t &t = (r->neg[n] ? del : add)
				[{r->hrel[n], r->harity[n]}];
			t = bdd_or(x[n], t);
		}
	}
	DBG(printdiff(wcout<<"add:"<<endl,add););
	DBG(printdiff(wcout<<"del:"<<endl,del););
	DBG(printdb(wcout<<"after step: "<<endl, this)<<endl;)
}

/*void lp::align(const db_t& d, size_t pbits, size_t bits) {
	if (bits == pbits) return;
	for (auto x : db) {
		auto it = d.find(x.first);
		if (it == d.end()) continue;
		*x.second = bdd_or(*x.second,
				bdd_rebit(*it->second, pbits, bits,
				arlen(x.first.second)*bits));
	}
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
//		align(prev->db, prev->bits, bits);
	}
	diff_t d, add, del, t;
	set<size_t> pf;
	size_t step = 0;
//	wcout << V.size() << endl;
	for (set<diff_t, diffcmp> s;;) {
		wcout << "step: " << step++ << endl;
		s.emplace(d = copy(db)), fwd(add, del);
		if (!bdd_and_not(add, del, t))
			return false; // detect contradiction
		for (auto x : add)
			add_fact(x.second, x.first.first, x.first.second);
		for (auto x : del)
			add_not_fact(x.second, x.first.first, x.first.second);
		if (db == d) break;
		if (s.find(copy(db)) != s.end()) return false;
	}
	if (delrel != -1) {
		set<pair<int_t, ints>> d;
		for (auto x : db) if (x.first.first==delrel) d.insert(x.first);
		for (auto x : d) db.erase(x);
	}
	DBG(printdb(wcout<<"after prog: "<<endl, this)<<endl;)
//	if (gbdd != F) db = bdd_and(gbdd, db);
	return true;
}

lp::~lp() {
//	for (rule* r : rules) delete r;
//	if (prev) delete prev;
//	if (proof1) delete proof1, delete proof2;
}

wostream& bdd_out(wostream& os,size_t n){
	return bdd_out(os<<L'['<<n<<L']',getnode(n));
}
wostream& bdd_out(wostream& os, const node& n) { //print bdd in ?: syntax
	return	nleaf(n) ? os << (ntrueleaf(n) ? L'T' : L'F') : (bdd_out(
		os<<n[0]<<L'?',getnode(n[1])),bdd_out(os<<L':',getnode(n[2])));
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
