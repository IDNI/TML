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
#include "term.h"
#ifdef DEBUG
#include "driver.h"
#else
#include "lp.h"
#endif
using namespace std;

void tml_init() { bdd_init(); }
DBG(wostream& printbdd(wostream& os, size_t t);)

void lp::add_fact(size_t f, const prefix& p) {
	size_t *t = db[p];
	if (!t) *(db[p] = new size_t) = f;
	else *t = bdd_or(*t, f);
}

bool lp::add_not_fact(size_t f, const prefix& p) {
	size_t *t = db[p], x = *t;
	return (*t = bdd_and_not(*t, f)), (x == F || *t != F);
}

bool lp::add_fact(const term& x) {
//	if (x.neg) return add_not_fact(fact(x, bits, dsz), x.rel, x.arity);
	return add_fact(fact(x, rng), x.pref()), true;
}

bool lp::add_facts(const matrix& x) {
	for (auto y : x) if (!add_fact(y)) return false; // FIXME
	return true;
}

size_t prefix_zeros(size_t x, size_t v, size_t k) {
	if (v) return bdd_add({k-v+1, F, prefix_zeros(x, v-1, k)});
	if (leaf(x)) return x;
	const node n = getnode(x);
	return bdd_add({n[0]+k, prefix_zeros(n[1],0,k),prefix_zeros(n[2],0,k)});
}

size_t prefix_zeros(size_t x, size_t k) { return prefix_zeros(x, k, k); }

db_t rebit(size_t pbits, size_t bits, db_t db) {
	if (pbits == bits) return db;
	assert(pbits < bits);
	for (auto x : db)
		*x.second = prefix_zeros(*x.second, (bits-pbits)*x.first.len());
	return db;
}

void bdd_or(diff_t& x, const term& t, range& rng) {
	auto it = x.find(t.pref());
	if (it == x.end()) it = x.emplace(t.pref(), F).first;
	it->second = bdd_or(it->second, fact(t, rng));
}

lp::lp(prog_data pd, range rng, lp *prev) : pd(pd), rng(rng) {
	if (prev) {
		db = rebit(prev->rng.bits, rng.bits, move(prev->db));
		delete prev;
	}
	//wcout<<r<<endl;
	for (const auto& m : pd.r) {
		for (const term& t : m.first)
			if (db.find({t.rel(), t.arity()}) == db.end())
				*(db[{t.rel(), t.arity()}] = new size_t) = F;
		for (const term& t : m.second)
			if (db.find({t.rel(), t.arity()}) == db.end())
				*(db[{t.rel(), t.arity()}] = new size_t) = F;
	}
	for (const auto& m : pd.r)
 		if (m.second.empty()) {
			if (!add_facts(m.first))
				// FIXME
//				(wcout << L"contradictory fact: "<<m[0]<<endl),
				exit(0);
		} else {
			vector<size_t*> dbs;
			for (size_t n = 0; n < m.second.size(); ++n)
				dbs.push_back(db[{m.second[n].rel(),
					m.second[n].arity()}]);
			rules.emplace_back(
				new rule(m.first, m.second, dbs, rng));
		}
//	DBG(printdb(wcout<<L"pos:"<<endl, this);)
//	DBG(printndb(wcout<<L"neg:"<<endl, this)<<endl;)
	for (auto x : pd.strtrees)
		strtrees[x.first][x.second.pref()] = fact(x.second, rng);
	for (const term& t : pd.goals) bdd_or(gbdd, t, rng);
	for (const term& t : pd.tgoals)
		trees.emplace(diff_t::key_type{t.rel(),t.arity()}, fact(t,rng));
}

void lp::fwd(diff_t &add, diff_t &del) {
	//DBG(printdb(wcout, this));
	map<prefix, vector<size_t>> a, d;
	for (rule* r : rules) {
		const sizes x = r->fwd();
		if (x.empty()) continue;
		for (size_t n = 0; n != x.size(); ++n)
			(r->neg[n] ? d : a)[r->hpref[n]].push_back(x[n]);
/*		for (size_t n = 0; n != x.size(); ++n) {
			size_t &t = (r->neg[n] ? del : add)[r->hpref[n]];
			t = bdd_or(x[n], t);
		}*/
	}
	for (auto x : a)
		x.second.push_back(add[x.first]),
		add[x.first] = bdd_or_many(x.second);
	for (auto x : d)
		x.second.push_back(del[x.first]),
		del[x.first] = bdd_or_many(x.second);
	//DBG(printdiff(wcout<<"add:"<<endl,add,rng.bits););
	//DBG(printdiff(wcout<<"del:"<<endl,del););
	//DBG(printdb(wcout<<"after step: "<<endl, this)<<endl;)
}

struct diffcmp {
	bool operator()(const diff_t& x, const diff_t& y) const {
		if (x.size() != y.size()) return x.size() < y.size();
		auto xt = x.begin(), yt = y.begin();
		while (xt != x.end())
			if (xt->first != yt->first) return xt->first<yt->first;
			else if (xt->second == yt->second) ++xt, ++yt;
			else return xt->second < yt->second;
		return false;
	}
};

diff_t copy(const db_t& x) {
	diff_t r;
	for (auto y : x) r[y.first] = *y.second;
	return r;
}

void copy(const diff_t& src, db_t& dst) {
	for (auto x : dst) delete x.second;
	dst.clear();
	for (auto x : src) dst.emplace(x.first, new size_t(x.second));
}

bool bdd_and_not(const diff_t& x, const diff_t& y, diff_t& r) {
	for (auto t : x)
		if (has(y, t.first) && t.second && F == (r[t.first] 
				= bdd_and_not(t.second, y.at(t.first))))
			return false;
	return true;
}

db_t& bdd_and_not(db_t& x, const diff_t& y) {
	for (auto t : x)
		if (has(y, t.first))
			*t.second = bdd_and_not(*t.second, y.at(t.first));
	return x;
}

void bdd_or(db_t& x, const diff_t& y) {
	for (auto t : x)
		if (has(y, t.first))
			*t.second = bdd_or(*t.second, y.at(t.first));
}

bool operator==(const db_t& x, const diff_t& y) {
	if (x.size() != y.size()) return false;
	auto xt = x.begin();
	auto yt = y.begin();
	while (xt != x.end())
		if (xt->first==yt->first && *xt->second==yt->second) ++xt, ++yt;
		else return false;
	return true;
}

bool lp::pfp() {
	diff_t d, add, del, t;
	set<size_t> pf;
	size_t step = 0;
//	wcout << V.size() << endl;
//	DBG(printdb(wcout<<"before prog: "<<endl, this)<<endl;)
	for (set<diff_t, diffcmp> s;;) {
		//DBG()
		wcout << "step: " << step++ << endl;
		s.emplace(d = copy(db)), fwd(add, del);
		if (!bdd_and_not(add, del, t))
			return false; // detect contradiction
		for (auto x : add) add_fact(x.second, x.first);
		for (auto x : del) add_not_fact(x.second, x.first);
		if (db == d) break;
		if (has(s, copy(db))) return false;
		if (memos > 1e+4) memos_clear();
	}
//	DBG(drv->printdiff(wcout<<"trees:"<<endl, trees, rng.bits);)
	get_trees();
//	DBG(static int nprog = 0;)
//	DBG(printdb(wcout<<"after prog: "<<nprog++<<endl, this)<<endl;)
	auto it = db.end();
	for (auto x : gbdd)
		if ((it = db.find(x.first)) != db.end()) {
			delete it->second;
			db.erase(it);
		}
	return true;
}

lp::~lp() { for (rule* r : rules) delete r; }
