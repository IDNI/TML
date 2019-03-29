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

template<typename T, typename V>
V& cat(V& v, const T& t) { return v.push_back(t), v; }

template<typename V>
V& cat(V& v, const V& t, size_t off = 0, size_t loff = 0, size_t roff = 0) {
	return v.insert(v.end()-off, t.begin()+loff, t.end()-roff), v;
}

size_t fact(term v, size_t bits) {
	if (v.arity == ints{0}) return T;
	size_t r = T;
	unordered_map<int_t, size_t> m;
	auto it = m.end();
	for (size_t j = 0; j != v.args.size(); ++j)
		if (v.args[j] >= 0) from_int_and(v.args[j], bits, j * bits, r);
		else if (m.end()==(it=m.find(v.args[j])))m.emplace(v.args[j],j);
		else for (size_t b = 0; b!=bits; ++b)
			r = bdd_and(r, from_eq(j*bits+b, it->second*bits+b));
	return v.neg ? bdd_and_not(T, r) : r;
}

void rule::get_varmap(const matrix& v) {
	size_t k = v[0].args.size(), i, j;
	hrel = v[0].rel, harity = v[0].arity;
	for (i = 1; i != v.size(); ++i)
		rels.push_back(v[i].rel), arities.push_back(v[i].arity);
	for (j = 0; j != v[0].args.size(); ++j)
		if (v[0].args[j] < 0 && varmap.end()==varmap.find(v[0].args[j]))
			varmap.emplace(v[0].args[j], j);
	for (i = 1; i != v.size(); ++i)
		for (j = 0; j != v[i].args.size(); ++j)
			if (v[i].args[j] < 0)
				if (varmap.find(v[i].args[j]) == varmap.end())
					varmap.emplace(v[i].args[j], k++);
	vars_arity = {(int_t)k};
}
/*
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
*/
rule::rule(matrix v, const vector<size_t*>& dbs, size_t bits, size_t /*dsz*/) :
	neg(v[0].neg), dbs(dbs), ae(bits, v[0]) {//, ext(get_extents(v, bits, dsz)) {
	get_varmap(v);
	//wcout<<v<<endl;
	size_t i, j, b;
	for (i = 1; i != v.size(); ++i) {
		size_t ar = v[i].args.size();
		sizes perm(bits * ar);
		for (j = 0; j != bits * ar; ++j) perm[j] = j;
		for (j = 0; j != ar; ++j)
			if (v[i].args[j] < 0)
				for (b = 0; b != bits; ++b)
					perm[b+j*bits]=
						b+varmap[v[i].args[j]]*bits;
		q.emplace_back(bits, v[i], move(perm));
	}
//	wcout << v << endl << vars << endl << endl;
//	drv->printbdd(wcout, v)<<endl, drv->printbdd(wcout, proof1)<<endl,
//	drv->printbdd(wcout, proof2), exit(0);
}

size_t rule::fwd(size_t bits) {
	size_t vars = T;
	sizes v(q.size());
	for (size_t n = 0; n < q.size(); ++n) 
		if (F == (v[n] = q[n](*dbs[n]))) return F;
//		DBG(else printbdd(wcout<<"q"<<n<<endl,v[n],vars_arity,hrel)<<endl;)
	if (F == (vars = bdd_and_many(v, 0, v.size()))) return F;
//	DBG(printbdd(wcout<<"q:"<<endl, vars,vars_arity,hrel)<<endl;)
//	vars = ext(vars);
//	DBG(printbdd(wcout<<"e:"<<endl, vars,vars_arity,hrel)<<endl;)
	vars = ae(bdd_deltail(vars, bits*arlen(harity)));
//	vars = ae(vars);
//	DBG(printbdd(wcout<<"ae:"<<endl, vars,vars_arity,hrel)<<endl;)
	return vars;
}
