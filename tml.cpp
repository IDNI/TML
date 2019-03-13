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
#ifdef DEBUG
#include "driver.h"
#else
#include "tml.h"
#endif
using namespace std;

#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."
#define vecfill(v,x,y,z) fill((v).begin() + (x), (v).begin() + (y), z)
#define veccat(x, y) (x).insert((x).end(), (y).begin(), (y).end())
void tml_init() { bdd_init(); }

wostream& out(wostream& os, const node& n) { //print bdd in ?: syntax
	return	nleaf(n) ? os << (ntrueleaf(n) ? L'T' : L'F') :
		(out(os<<n[0]<<L'?',getnode(n[1])),out(os<<L':',getnode(n[2])));
}
wostream& out(wostream& os,size_t n){return out(os<<L'['<<n<<L']',getnode(n));}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x){ os << (y?1:0); } return os; }
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) { os << y << endl; } return os; }
wostream& operator<<(wostream& os, const matrix& m) {
	for (const term& t : m) {
		for (auto x : t) wcout << x << ',';
		wcout << endl;
	}
	return os;
}

struct vbcmp {
	bool operator()(const vector<bool>* x, const vector<bool>* y) const {
		return *x < *y;
	}
};

#ifdef DEBUG
std::wostream& printbdd(std::wostream& os, size_t t);
#endif

struct rule { // a P-DATALOG rule in bdd form
	struct body {
		size_t sel = T;
		const bool neg;
		bools ex;
		vector<size_t> perm;
		body(term &t, size_t ar, size_t bits, size_t dsz, size_t nvars);
		void from_arg(int_t vij, size_t j, size_t bits, size_t dsz,
			map<int_t, size_t>& m);
		size_t varbdd(size_t db, lp::step& p) const {
			auto it = (neg ? p.neg : p.pos).find({sel, ex});
			if (it != (neg?p.neg:p.pos).end())
				return bdd_permute(it->second, perm);
			size_t r = (neg?bdd_and_not:bdd_and)(sel, db);
			r = bdd_ex(r, ex);
			(neg ? p.neg : p.pos).emplace(make_pair(sel,ex), r);
			r = bdd_permute(r, perm);
			//DBG(printbdd(wcout, r);)
			return r;
		}
	};
	bool neg = false;
	size_t hsym = T;
	vector<body> bd;

	rule() {}
	rule(rule&& r) : neg(r.neg), hsym(r.hsym) {}
	rule(matrix v, size_t bits, size_t dsz, set<matrix>* proof = 0);
	size_t fwd(size_t db, size_t bits, size_t ar, lp::step& s,
		set<size_t>* p) const;
};

#define from_int_and(x, y, o, r) r = bdd_and(r, from_int(x, y, o))
size_t from_int(size_t x, size_t bits, size_t offset) {
	size_t r = T, b = bits--;
	while (b--) r = bdd_and(r, from_bit(bits - b + offset, x&(1<<b)));
	return r;
}

void from_eq(size_t src, size_t dst, size_t len, size_t &r) {
	while (len--) r = bdd_and(r, from_eq(src + len, dst + len));
}

void from_range(size_t max, size_t bits, size_t offset, size_t &r) {
	size_t x = F;
	for (size_t n = 1; n < max; ++n) x = bdd_or(x,from_int(n,bits,offset));
	r = bdd_and(r, x);
}

void lp::rule_add(const matrix& x, set<matrix>* proof) {
 	if (x.size() == 1) db = bdd_or(db, rule(x, bits, dsz).hsym);//fact
	else rules.emplace_back(new rule(x, bits, dsz, proof));
}

size_t varcount(const matrix& v) { // bodies only
	set<int_t> vars;
	for (const term& x : v) 
		for (size_t i = 1; i != x.size(); ++i) 
			if (x[i] < 0) vars.emplace(x[i]);
	return vars.size();
}

rule::body::body(term &t, size_t ar, size_t bits, size_t dsz, size_t nvars)
	: neg(t[0] < 0) {
	map<int_t, size_t> m;
	size_t b, j;
	t.erase(t.begin()),ex.resize(bits*ar,false),perm.resize((ar+nvars)*bits);
	for (b = 0; b != (ar + nvars) * bits; ++b) perm[b] = b;
	for (j = 0; j != ar; ++j) from_arg(t[j], j, bits, dsz, m);
}

void rule::body::from_arg(int_t vij, size_t j, size_t bits, size_t dsz,
	map<int_t, size_t>& m) {
	auto it = m.end();
	if (vij >= 0) // sym
		vecfill(ex, j * bits, (j+1) * bits, true),
		from_int_and(vij, bits, j * bits, sel);
	else if ((it = m.find(vij)) != m.end()) //seen var
		vecfill(ex, j * bits, (j+1) * bits, true),
		from_eq(j * bits, it->second * bits, bits, sel);
	else	m.emplace(vij, j), from_range(dsz, bits, j * bits, sel);
}

rule::rule(matrix v, size_t bits, size_t dsz, set<matrix> *proof) {
	size_t i, j, b, ar = v[0].size() - 1, k = ar, nvars;
	neg = v[0][0] < 0, v[0].erase(v[0].begin()), nvars = varcount(v);
	for (i = 1; i != v.size(); ++i) // init, sel, ex and local eq
		bd.emplace_back(v[i], ar, bits, dsz, nvars);
	map<int_t, size_t> m;
	auto it = m.end();
	for (j = 0; j != ar; ++j) // hsym
		if (v[0][j] >= 0) from_int_and(v[0][j], bits, j * bits, hsym);
		else if (m.end() == (it=m.find(v[0][j]))) m.emplace(v[0][j], j);
		else from_eq(j * bits, it->second*bits, bits, hsym);
	for (i = 0; i != v.size() - 1; ++i) // var permutations
		for (j = 0; j != ar; ++j)
			if (v[i+1][j] < 0) {
				if ((it = m.find(v[i+1][j])) == m.end())
					it = m.emplace(v[i+1][j], k++).first;
				for (b = 0; b != bits; ++b)
					bd[i].perm[b+j*bits]=b+it->second*bits;
			}
	if (!proof) return;
	if (neg) er(err_proof);
	for (const body& b : bd) if (b.neg) er(err_proof);
	matrix prf;
	prf.resize(2), prf[0].push_back(1),
	prf[1].push_back(1), veccat(prf[0], v[0]), veccat(prf[1], v[0]);
	for (auto x : m) if (x.second >= ar) prf[1].push_back(x.first);
	for (i = 0; i < bd.size(); ++i) veccat(prf[0], v[i+1]);
	proof->emplace(prf);
}

size_t rule::fwd(size_t db, size_t bits, size_t ar, lp::step& s, set<size_t>* p)
	const {
	size_t vars;
	vector<size_t> v;
	if (bd.size() == 1) {
		if (F==(vars=bdd_and(hsym, bd[0].varbdd(db, s)))) return false;
		goto ret;
	}
	if (bd.size() == 2) {
		if (F == (vars = bdd_and(hsym, bdd_and(bd[0].varbdd(db, s),
			bd[1].varbdd(db, s))))) return false;
		goto ret;
	}
	for (const body& b : bd) {
		if (F == (vars = b.varbdd(db, s))) return F;
		v.push_back(vars);
	}
	v.push_back(hsym);
	if (F == (vars = bdd_and_many(v))) return false;
ret:	if (p) p->emplace(vars);
	//DBG(printbdd(wcout, vars);)
	return bdd_deltail(vars, bits * ar);
}

void lp::fwd(size_t &add, size_t &del, set<size_t>* pr) {
	p.pos.clear(), p.neg.clear();
	for (const rule* r : rules)
		(r->neg?del:add)=bdd_or(r->fwd(db,bits,ar,p,pr),r->neg?del:add);
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
			if (r[n][i] == pad) break;
		}
	return r;
}

matrix lp::getdb() const { return getbdd(db); }
matrix lp::getbdd(size_t t) const { return from_bits(t, bits, ar); }
lp::~lp() { for (rule* r : rules) delete r; }

size_t std::hash<std::pair<size_t, bools>>::operator()(
	const std::pair<size_t, bools>& m) const {
	std::hash<size_t> h1;
	std::hash<bools> h2;
	return h1(m.first) + h2(m.second);
}
