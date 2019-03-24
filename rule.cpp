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
#include <algorithm>
#include "rule.h"
#ifdef DEBUG
#include "driver.h"
#endif
using namespace std;

#define from_int_and(x, y, o, r) r = bdd_and(r, from_int(x, y, o))
#define vecfill(v,x,y,z) fill((v).begin() + (x), (v).begin() + (y), z)
#define symcat(x, y) ((x).push_back(y), (x))
#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."

int_t null, openp, closep;
template<typename T, typename V>
V& cat(V& v, const T& t) { return v.push_back(t), v; }

template<typename V>
V& cat(V& v, const V& t, size_t off = 0, size_t loff = 0, size_t roff = 0) {
	return v.insert(v.end()-off, t.begin()+loff, t.end()-roff), v;
}

size_t fact(term v, size_t bits) {
	size_t r = T;
	unordered_map<int_t, size_t> m;
	auto it = m.end();
	for (size_t j = 0; j != v.size() - 1; ++j)
		if (v[j+1] >= 0) from_int_and(v[j+1], bits, j * bits, r);
		else if (m.end() == (it = m.find(v[j+1]))) m.emplace(v[j+1],j);
		else for (size_t b = 0; b!=bits; ++b)
			r = bdd_and(r, from_eq(j*bits+b, it->second*bits+b));
	return v[0] < 0 ? bdd_and_not(T, r) : r;
}

size_t varcount(const matrix& v) { // bodies only
	set<int_t> vars;
	for (const term& x : v) 
		for (size_t i = 1; i != x.size(); ++i) 
			if (x[i] < 0) vars.emplace(x[i]);
	return vars.size();
}

unordered_map<int_t, size_t> rule::get_varmap(const matrix& v) {
	unordered_map<int_t, size_t> m;
	size_t ar = v[0].size() - 1, k = ar, i, j;
	for (j = 0; j != ar; ++j)
		if (v[0][j+1] < 0 && m.end() == m.find(v[0][j+1]))
			m.emplace(v[0][j+1], j);
	for (i = 0; i != v.size() - 1; ++i)
		for (j = 0; j != ar; ++j)
			if (v[i+1][j+1] < 0)
				if (m.find(v[i+1][j+1]) == m.end())
					m.emplace(v[i+1][j+1], k++);
	return vars_arity = k, m;
}

extents rule::get_extents(const matrix& v, size_t bits, size_t dsz) {
	size_t ar = v[0].size()-1, l = 0;
	term excl = {pad, openp, closep}, lt(ar, 0), gt(ar, 0);
	sizes succ(ar, 0), pred(ar, 0), dom;
	for (auto x : varmap) dom.push_back(x.second), l = max(l, x.second);
	dom.push_back(l + 1);
	for (size_t n = 1; n != v.size(); ++n)
		if (v[n][0] < 0)
			for (size_t k = 0; k != ar; ++k)
				lt[varmap[v[n][k+1]]] = dsz;
	return extents(bits,vars_arity,ar*bits,dom,dsz,0,excl,lt,gt,succ,pred);
}

rule::rule(matrix v, size_t bits, size_t dsz, bool proof) :
	neg(v[1][0] < 0), varmap(get_varmap(v)), ae(bits, v[0])
	, ext(get_extents(v, bits, dsz)) {
	//wcout<<v<<endl;
	size_t ar = v[0].size()-1, i, j, b;
	v[0].erase(v[0].begin());
	for (i = 0; i != v.size() - 1; ++i) {
		sizes perm(bits * ar);
		for (j = 0; j != bits * ar; ++j) perm[j] = j;
		for (j = 0; j != ar; ++j)
			if (v[i+1][j+1] >= 0) continue;
			else for (b = 0; b != bits; ++b)
				perm[b+j*bits]=b+varmap[v[i+1][j+1]]*bits;
		q.emplace_back(bits, v[i+1], move(perm));
	}

	if (!proof) return;
	for (i = 0; i != v.size(); ++i)
		if (v[i][0] < 0) er(err_proof);
		else if (i) v[i].erase(v[i].begin());

	term vars, prule, bprule, x, y;
	set<size_t> vs;
	for (int_t t : v[0]) if (t < 0) vs.insert(t);
	cat(cat(vars, 1), v[0]), cat(cat(prule, 1), openp), cat(bprule, 1);
	//for (auto x : m) if (x.second >= ar) cat(vars, x.first);
	for (i = 1; i != v.size(); ++i)
		for (int_t t : v[i])
			if (t < 0 && vs.find(t) == vs.end())
				vs.insert(t), cat(vars, t);
	//for (term& t : v) while (t[t.size()-1] == pad) t.erase(t.end()-1);
	for (i = 0; i != v.size(); ++i) cat(prule, v[i]);
	cat(prule, closep), cat(bprule, v[0]), cat(bprule, openp);
	for (i = 1; i != v.size(); ++i) cat(bprule, v[i]);
	cat(bprule, closep);

	proof1 = {{prule},{vars}};
	matrix r = { bprule, prule, cat(cat(cat(y={1}, openp), v[0]), closep) };
	for (i = 1; i != v.size(); ++i)
		proof2.insert({
			cat(cat(cat(x={1}, openp), v[i]), closep),
			prule, r[2]}),
//			cat(cat(cat(y={1}, openp), v[0]), closep)}),
		r.push_back(cat(cat(cat(x={1}, openp), v[i]), closep));
	proof2.insert(move(r));
//	wcout << v << endl << vars << endl << endl;
//	drv->printbdd(wcout, v)<<endl, drv->printbdd(wcout, proof1)<<endl,
//	drv->printbdd(wcout, proof2), exit(0);
}

size_t rule::fwd(size_t db, size_t bits, size_t ar, lp::step&) {
	size_t vars = T;
	sizes v(q.size());
	size_t i = 0;
	for (query& x : q)
		if (F == (v[i++] = x(db))) return F;
		DBG(else printbdd(wcout<<"q"<<i-1<<endl,v[i-1],bits,vars_arity)<<endl;)
	if (F == (vars = bdd_and_many(v, 0, v.size()))) return F;
	DBG(printbdd(wcout<<"q:"<<endl, vars,bits,vars_arity)<<endl;)
	vars = ext(vars);
	DBG(printbdd(wcout<<"e:"<<endl, vars,bits,vars_arity)<<endl;)
	//vars = ae(bdd_deltail(vars, bits*ar));
	vars = ae(vars);
	DBG(printbdd(wcout<<"ae:"<<endl, drv->prog, vars)<<endl;)
	if (!proof2.empty()) p.emplace(vars);
	return vars;
}

size_t rule::get_varbdd(size_t bits, size_t ar) const {
	size_t x = T, y = F, n;
	for (size_t z : p) y = bdd_or(y, z);
//	DBG(printbdd_one(wcout<<"rule::get_varbdd"<<endl, y);)
	for (n = vars_arity; n != ar; ++n) from_int_and(pad, bits, n*bits, x);
//	DBG(printbdd_one(wcout<<"rule::get_varbdd"<<endl, bdd_and(x, y));)
	return bdd_and(x, y);
}

size_t std::hash<std::pair<size_t, bools>>::operator()(
	const std::pair<size_t, bools>& m) const {
	std::hash<size_t> h1;
	std::hash<bools> h2;
	return h1(m.first) + h2(m.second);
}
