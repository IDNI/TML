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
#include "rule.h"
#ifdef DEBUG
#include "driver.h"
#endif
using namespace std;

#define from_int_and(x, y, o, r) r = bdd_and(r, from_int(x, y, o))
#define vecfill(v,x,y,z) fill((v).begin() + (x), (v).begin() + (y), z)
#define veccat(x, y) (x).insert((x).end(), (y).begin(), (y).end())
#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."

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
	//DBG(printbdd(wcout <<"sel: " << endl, sel)<<endl;)
	if (it != (neg?p.neg:p.pos).end()) return bdd_permute(it->second, perm);
	size_t r = (neg?bdd_and_not:bdd_and)(sel, db), n;
	if (r == F) goto ret;
	n = eqs.size();
	while (n) if (F == (r = bdd_and(r, eqs[--n]))) goto ret;
	r = bdd_ex(r, ex);
ret:	(neg ? p.neg : p.pos).emplace(make_pair(r, ex), r);
	return r == F ? F : bdd_permute(r, perm);
}

rule::rule(matrix v, size_t bits, size_t dsz, const matrices& /*pgoals*/) {
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
/*	if (!prf || v.size() == 1) return;
	if (neg) er(err_proof);
	for (const body& b : bd) if (b.neg) er(err_proof);
	proof.resize(2), proof[0].push_back(1), proof[1].push_back(1),
	veccat(proof[0], v[0]), veccat(proof[1], v[0]);
	for (auto x : m) if (x.second >= ar) proof[1].push_back(x.first);
	for (i = 0; i != bd.size(); ++i) veccat(proof[0], v[i+1]);*/
//	for (j = 0; j != prf[0].size(); ++j)
//		if (prf[0][j] == pad) prf[0].erase(prf[0].begin()+j--);
//	for (i = 0; i != prf.size(); ++i)
//		proof_arity = max(proof_arity, prf[i].size() - 1);
//	proof_arity = v.size() * ar;
	DBG(wcout << proof << endl;)
}

size_t rule::fwd(size_t db, size_t bits, size_t ar, lp::step& s) {
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
/*ret:*/if (!proof.empty()) p.emplace(vars);
//	wcout<<"vars solutions#: " << bdd_count(vars, vars_arity * bits) << endl;
	DBG(printbdd_one(wcout<<"one: ", vars, bits, vars_arity);)
/*	wcout<<"vars solutions#: " << bdd_count(bdd_deltail(vars, bits * ar),
		ar * bits) << endl;
	DBG(printbdd(wcout, bdd_deltail(vars, bits * ar));)*/
	return bdd_deltail(vars, bits * ar);
}

size_t rule::get_varbdd(size_t bits, size_t ar) const {
	size_t x = T, y = F, n;
	for (size_t z : p) y = bdd_or(y, z);
	DBG(printbdd_one(wcout<<"rule::get_varbdd"<<endl, y);)
	for (n = vars_arity; n != ar; ++n) from_int_and(pad, bits, n*bits, x);
	DBG(printbdd_one(wcout<<"rule::get_varbdd"<<endl, bdd_and(x, y));)
	return bdd_and(x, y);
}
