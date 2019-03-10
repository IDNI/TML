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
#include "tml.h"
using namespace std;

void tml_init() { bdd_init(); }

matrix from_bits(size_t x, size_t bits, size_t ar);
wostream& out(wostream& os, const node& n) { //print using ?: syntax
	return	nleaf(n) ? os << (ntrueleaf(n) ? L'T' : L'F') :
		(out(os<<n[0]<<L'?',getnode(n[1])),out(os<<L':',getnode(n[2])));
}
wostream& out(wostream& os,size_t n){return out(os<<L'['<<n<<L']',getnode(n));}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x){ os << (y?1:0); } return os; }
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) { os << y << endl; } return os; }

struct vbcmp {
	bool operator()(const vector<bool>* x, const vector<bool>* y) const {
		return *x < *y;
	}
};

struct rule { // a P-DATALOG rule in bdd form
	struct body {
		size_t sel = T;
		const bool neg;
		bools ex; 
		vector<size_t> perm;
		body(bool neg) : neg(neg) {}
		size_t varbdd(size_t db, lp::step& p) const {
			auto it = (neg ? p.neg : p.pos).find({sel, ex});
			if (it != (neg?p.neg:p.pos).end())
				return bdd_permute(it->second, perm);
			size_t r = (neg?bdd_and_not_ex:bdd_and_ex)(sel, db, ex);
			(neg ? p.neg : p.pos).emplace(make_pair(sel,ex), r);
			return bdd_permute(r, perm);
		}
	};
	bool neg = false;
	size_t hsym = T, *sels = 0;
	vector<body> bd;

	rule() {}
	rule(rule&& r) : neg(r.neg), hsym(r.hsym) { r.sels = 0; }
	rule(matrix v, size_t bits, size_t dsz);
	size_t fwd(size_t db, size_t bits, size_t ar, lp::step& s) const;
	~rule() { if (sels) delete sels; }
};

size_t from_int(size_t x, size_t bits, size_t offset) {
	size_t r = T, b = bits--;
	while (b--) r = bdd_and(r, from_bit(bits - b + offset, x&(1<<b)));
	return r;
}

size_t from_range(size_t max, size_t bits, size_t offset) {
	size_t x = F;
	for (size_t n = 1; n < max; ++n) x = bdd_or(x,from_int(n,bits,offset));
	return x;
}

void lp::rule_add(const matrix& x) {
 	if (x.size() == 1) db = bdd_or(db, rule(x, bits, dsz).hsym);//fact
	else rules.emplace_back(new rule(x, bits, dsz));
}

rule::rule(matrix v, size_t bits, size_t dsz) {
	size_t i, j, b, ar = v[0].size() - 1, k = ar, nvars;
	neg = v[0][0] < 0;
	v[0].erase(v[0].begin());
	set<int_t> vars;
	for (term& x : v) 
		for (i = 1; i != x.size(); ++i) 
			if (x[i] < 0) vars.emplace(x[i]);
	nvars = vars.size();
	map<int_t, size_t> m;
	auto it = m.end();
	for (i = 1; i != v.size(); ++i) { // init, sel, ex and local eq
		body d(v[i][0] < 0);
		v[i].erase(v[i].begin()),
		d.ex = bools(bits * ar, false);
		d.perm.resize((ar + nvars) * bits);
		for (b = 0; b != (ar + nvars) * bits; ++b) d.perm[b] = b;
		for (j = 0; j != ar; ++j)
			if (v[i][j] >= 0) {
				d.sel = bdd_and(d.sel,
					from_int(v[i][j], bits, j * bits));
				for (b = 0; b != bits; ++b) d.ex[b+j*bits]=true;
			} else if ((it = m.find(v[i][j])) != m.end())
				for (b = 0; b != bits; ++b)
					d.ex[b+j*bits] = true,
					d.sel = bdd_and(d.sel, from_eq(b+j*bits,
						b+it->second*bits));
			else 	m.emplace(v[i][j], j), d.sel = bdd_and(d.sel,
					from_range(dsz, bits, j * bits));
		m.clear(), bd.push_back(move(d));
	}
	for (j = 0; j != ar; ++j) // hsym
		if (v[0][j] >= 0)
			hsym = bdd_and(hsym, from_int(v[0][j], bits, j * bits));
		else if (m.end() == (it=m.find(v[0][j]))) m.emplace(v[0][j], j);
		else for (b = 0; b != bits; ++b)
			hsym=bdd_and(hsym,from_eq(b+j*bits, b+it->second*bits));
	for (i = 0; i != v.size() - 1; ++i) // var permutations
		for (j = 0; j != ar; ++j)
			if (v[i+1][j] < 0) {
				if ((it = m.find(v[i+1][j])) == m.end())
					it = m.emplace(v[i+1][j], k++).first;
				for (b = 0; b != bits; ++b)
					bd[i].perm[b+j*bits]=b+it->second*bits;
			}
	if (v.size() > 1) sels = new size_t[v.size() - 1];
}

size_t rule::fwd(size_t db, size_t bits, size_t ar, lp::step& s) const {
	size_t vars = T;
	for (const body& b : bd)
		if (F == (vars = bdd_and(vars, b.varbdd(db, s)))) return F;
	return bdd_and_deltail(hsym, vars, bits * ar);
}

void lp::fwd() {
	size_t add = F, del = F, s;
	p.pos.clear(), p.neg.clear();
	for (const rule* r : rules)
		(r->neg?del:add)=bdd_or(r->fwd(db, bits, ar, p),r->neg?del:add);
	if ((s = bdd_and_not(add, del)) == F && add != F)
		db = F; // detect contradiction
	else db = bdd_or(bdd_and_not(db, del), s);
}

bool lp::pfp() {
	size_t d;
	vector<int_t> v;
	for (set<int_t> s;;)
		if (s.emplace(d = db), fwd(), s.find(db) != s.end())
			return d == db;
}

matrix lp::getdb() { return from_bits(db, bits, ar); }

matrix from_bits(size_t x, size_t bits, size_t ar) {
	vbools s = allsat(x, bits * ar);
	matrix r(s.size());
	for (term& v : r) v = term(ar, 0);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i)
			for (b = 0; b != bits; ++b)
				if (s[n][i * bits + b])
					r[n][i] |= 1 << (bits - b - 1);
	return r;
}

size_t std::hash<std::pair<size_t, bools>>::operator()(
	const std::pair<size_t, bools>& m) const {
	std::hash<size_t> h1;
	std::hash<bools> h2;
	return h1(m.first) + h2(m.second);
}
