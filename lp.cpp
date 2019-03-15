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
#include "defs.h"
#ifdef DEBUG
#include "driver.h"
#else
#include "lp.h"
#endif
using namespace std;

#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."
#define vecfill(v,x,y,z) fill((v).begin() + (x), (v).begin() + (y), z)
#define veccat(x, y) (x).insert((x).end(), (y).begin(), (y).end())
int_t pad = 0;
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
		for (auto x : t) os << x << ',';
		os << endl;
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
		vector<size_t> perm, eqs;
		body(term &t, size_t ar, size_t bits, size_t dsz, size_t nvars);
		void from_arg(int_t vij, size_t j, size_t bits, size_t dsz,
			map<int_t, size_t>& m);
		size_t varbdd(size_t db, lp::step& p) const;
	};
	bool neg = false;
	size_t hsym = T, proof_arity = 0, vars_arity;
	vector<body> bd;
	vector<size_t> eqs;
	set<size_t> p;

	rule() {}
//	rule(rule&& r) : neg(r.neg), hsym(r.hsym) {}
	rule(matrix v, size_t bits, size_t dsz, set<matrix>* proof);
	size_t fwd(size_t db, size_t bits, size_t ar, lp::step& s, 
		set<size_t>* proof);
	size_t get_varbdd(size_t bits, size_t ar) const;
};

void from_range(size_t max, size_t bits, size_t offset, size_t &r) {
	size_t x = F;
	for (size_t n = 1; n < max; ++n) x = bdd_or(x,from_int(n,bits,offset));
	r = bdd_and(r, x);
}

void lp::rule_add(const matrix& x, set<matrix>* proof) {
 	if (x.size() == 1) db = bdd_or(db, rule(x, bits, dsz, 0).hsym);//fact
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
	: neg(t[0] < 0) { // init, sel, ex and local eq
	map<int_t, size_t> m;
	size_t b, j;
	t.erase(t.begin()), 
	ex.resize(bits*ar,false), perm.resize((ar+nvars)*bits);
	for (b = 0; b != (ar + nvars) * bits; ++b) perm[b] = b;
	for (j = 0; j != ar; ++j) from_arg(t[j], j, bits, dsz, m);
}

void rule::body::from_arg(int_t vij, size_t j, size_t bits, size_t dsz,
	map<int_t, size_t>& m) {
	auto it = m.end();
	vector<array<size_t, 2>> eq;
	if (vij >= 0) // sym
		vecfill(ex, j * bits, (j+1) * bits, true),
		from_int_and(vij, bits, j * bits, sel);
	else if ((it = m.find(vij)) != m.end()) { //seen var
		vecfill(ex, j * bits, (j+1) * bits, true);
		for (size_t b = 0; b != bits; ++b)
			eq.emplace_back(array<size_t, 2>
				{j*bits+b, it->second*bits+b});
	} else	m.emplace(vij, j), from_range(dsz, bits, j * bits, sel);
	for (size_t i = 0; i != eq.size(); ++i) {
		if (!(i % 8)) eqs.push_back(T);
		eqs.back() = bdd_and(eqs.back(), from_eq(eq[i][0], eq[i][1]));
	}
}

size_t rule::body::varbdd(size_t db, lp::step& p) const {
	auto it = (neg ? p.neg : p.pos).find({sel, ex});
	if (it != (neg?p.neg:p.pos).end()) return bdd_permute(it->second, perm);
	size_t r = (neg?bdd_and_not:bdd_and)(sel, db), n = eqs.size();
	while (n) if (F == (r = bdd_and(r, eqs[--n]))) return false;
//	DBG(printbdd(wcout <<"r: " << endl, r)<<endl;)
	r = bdd_ex(r, ex);
	(neg ? p.neg : p.pos).emplace(make_pair(r, ex), r);
	return r = bdd_permute(r, perm);
}

rule::rule(matrix v, size_t bits, size_t dsz, set<matrix> *proof) {
	size_t i, j, b, ar = v[0].size() - 1, k = ar, nvars;
	neg = v[0][0] < 0, v[0].erase(v[0].begin()), nvars = varcount(v);
	for (i = 1; i != v.size(); ++i)
		bd.emplace_back(v[i], ar, bits, dsz, nvars);
	vector<array<size_t, 2>> heq;
	map<int_t, size_t> m;
	auto it = m.end();
	for (j = 0; j != ar; ++j) // hsym
		if (v[0][j] >= 0) from_int_and(v[0][j], bits, j * bits, hsym);
		else if (m.end() == (it=m.find(v[0][j]))) m.emplace(v[0][j], j);
		else for (b = 0; b!=bits; ++b)
			heq.emplace_back(array<size_t, 2>
				{j * bits + b, it->second * bits + b});
	for (j = 0; j != heq.size(); ++j) {
		if (!(j % 8)) eqs.push_back(T);
		eqs.back() = bdd_and(eqs.back(), from_eq(heq[j][0], heq[j][1]));
	}
	for (i = 0; i != v.size() - 1; ++i) // var permutations
		for (j = 0; j != ar; ++j)
			if (v[i+1][j] < 0) {
				if ((it = m.find(v[i+1][j])) == m.end())
					it = m.emplace(v[i+1][j], k++).first;
				for (b = 0; b != bits; ++b)
					bd[i].perm[b+j*bits]=b+it->second*bits;
			}
	vars_arity = k;
	DBG(wcout << v << endl;)
	if (!proof || v.size() == 1) return;
	if (neg) er(err_proof);
	for (const body& b : bd) if (b.neg) er(err_proof);
	matrix prf;
	prf.resize(2), prf[0].push_back(1), prf[1].push_back(1),
	veccat(prf[0], v[0]), veccat(prf[1], v[0]);
	for (auto x : m) if (x.second >= ar) prf[1].push_back(x.first);
	for (i = 0; i != bd.size(); ++i) veccat(prf[0], v[i+1]);
	for (j = 0; j != prf[0].size(); ++j)
		if (prf[0][j] == pad) prf[0].erase(prf[0].begin()+j--);
	for (i = 0; i != prf.size(); ++i)
		proof_arity = max(proof_arity, prf[i].size() - 1);
	DBG(wcout << prf << endl;)
	proof->emplace(prf);
}

size_t rule::fwd(size_t db, size_t bits, size_t ar, lp::step& s,
	set<size_t>* proof) {
	size_t vars = T, n;
/*	vector<size_t> v;
	if (bd.size() == 1) {
		if (F == (vars = bd[0].varbdd(db, s))) return false;
		for (size_t n = eqs.size(); n; ++n)
			if (F == (vars = bdd_and(vars, eqs[n]))) return false;
		vars = bdd_and(vars, hsym);
		goto ret;
	}
	if (bd.size() == 2) {
		if (F == (vars = bdd_and(bd[0].varbdd(db, s),
			bd[1].varbdd(db, s)))) return false;
		for (size_t n = eqs.size(); n; ++n)
			if (F == (vars = bdd_and(vars, eqs[n]))) return false;
		vars = bdd_and(vars, hsym);
		goto ret;
	}*/
	for (const body& b : bd) {
		if (F == (vars = bdd_and(vars, b.varbdd(db, s)))) return F;
//		v.push_back(vars);
	}
	for (n=eqs.size(); n;) if (F==(vars=bdd_and(vars, eqs[--n]))) return F;
	vars = bdd_and(vars, hsym);
//	v.push_back(hsym);
//	if (F == (vars = bdd_and_many(v))) return false;
/*ret:*/if (proof) p.emplace(vars);
//	wcout<<"vars solutions#: " << bdd_count(vars, vars_arity * bits) << endl;
	DBG(printbdd_one(wcout<<"one: ", vars, bits, vars_arity);)
/*	wcout<<"vars solutions#: " << bdd_count(bdd_deltail(vars, bits * ar),
		ar * bits) << endl;
	DBG(printbdd(wcout, bdd_deltail(vars, bits * ar));)*/
	return bdd_deltail(vars, bits * ar);
}

void lp::fwd(size_t &add, size_t &del, set<size_t>* pf) {
	p.pos.clear(), p.neg.clear();
	for (rule* r : rules)
		(r->neg?del:add)=bdd_or(r->fwd(db,bits,ar,p,pf),r->neg?del:add);
}

size_t rule::get_varbdd(size_t bits, size_t ar) const {
	size_t x = T, y = F, n;
	for (size_t z : p) y = bdd_or(y, z);
	DBG(printbdd_one(wcout<<"rule::get_varbdd"<<endl, y);)
	for (n = vars_arity; n != ar; ++n) from_int_and(pad, bits, n*bits, x);
	DBG(printbdd_one(wcout<<"rule::get_varbdd"<<endl, bdd_and(x, y));)
	return bdd_and(x, y);
}

size_t lp::get_varbdd() const {
	size_t t = F;
	for (const rule* r : rules)
		t = bdd_or(r->get_varbdd(bits, proof_arity()), t);
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

size_t lp::proof_arity() const {
	size_t r = 0;
	for (const rule* x : rules) r = max(r, x->proof_arity);
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
