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

size_t fact(term v, size_t bits, size_t dsz) {
//	DBG(wcout<<"add fact:"<<v<<endl;)
	if (v.arity == ints{0}) return T;
	size_t r = T;
	unordered_map<int_t, size_t> m;
	auto it = m.end();
	for (size_t j = 0; j != v.args.size(); ++j)
		if (v.args[j] >= 0) from_int_and(v.args[j], bits, j * bits, r);
		else if (m.end()==(it=m.find(v.args[j])))m.emplace(v.args[j],j);
	sizes domain;
	for (auto x : m) domain.push_back(x.second);
	r = builtins<leq_const>(bits, v.args.size()*bits,
		leq_const(domain, dsz-1, bits))(r);
	for (size_t j = 0; j != v.args.size(); ++j)
		if (v.args[j] < 0) for (size_t b = 0; b!=bits; ++b)
			if (j != m[v.args[j]])
				r = bdd_and(r,
					from_eq(j*bits+b, m[v.args[j]]*bits+b));
	if (v.neg) r = bdd_and_not(T, r);
	DBG(printbdd(wcout<<"before range:"<<endl, r, v.arity, v.rel)<<endl;)
	//if (domain.empty()) return dsz ? r : F;
	DBG(printbdd(wcout<<"ret:"<<endl, r, v.arity, v.rel)<<endl;)
	return r;
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

rule::rule(matrix v, const vector<size_t*>& dbs, size_t bits, size_t dsz) :
	neg(v[0].neg), dbs(dbs), ae(bits, v[0]) {
	get_varmap(v);
	set<int_t> vs;
	for (auto& x : v)
		for (int_t i : x.args)
			if (i < 0) vs.insert(i);
	if (!v[0].neg) {
		for (size_t n = 1; n != v.size(); ++n)
			if (!v[n].neg) for (int_t i : v[n].args)
				if (i < 0) vs.erase(i);
		if (!vs.empty()) {
			sizes domain;
			for (int_t i : vs) domain.push_back(varmap[i]);
			bts = new builtins<leq_const>(bits,
				bits*arlen(vars_arity),
//				bits*arlen(harity),
				leq_const(domain, dsz-1, bits));
		}
	}
	//wcout<<v<<endl;
	size_t i, j, b;
	for (i = 1; i != v.size(); ++i) {
		if (v[i].b != term::NONE) {
			function<int(int)> f;
			switch (v[i].b) {
				case term::ALPHA: f = ::isalpha; break;
				case term::DIGIT: f = ::isdigit; break;
				case term::ALNUM: f = ::isalnum; break;
				case term::SPACE: f = ::isspace; break;
				default: throw 0;
			}
			unary_builtins.emplace_back(
				builtins<unary_builtin<function<int(int)>>>(
				bits,bits*arlen(vars_arity),
				unary_builtin<function<int(int)>>(
				{varmap[v[i].args[0]]},v[i].neg,f,0,256,bits)));
			continue;
		}
		size_t ar = v[i].args.size();
		sizes perm(bits * ar);
		for (j = 0; j != bits * ar; ++j) perm[j] = j;
		for (j = 0; j != ar; ++j)
			if (v[i].args[j] < 0)
				for (b = 0; b != bits; ++b)
					perm[b+j*bits]=
						b+varmap[v[i].args[j]]*bits;
		q.emplace_back(bits, v[i], move(perm), v[i].neg);
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
	for (size_t n = 0; n != unary_builtins.size(); ++n)
		vars = unary_builtins[n](vars);
	if (bts) vars = ae(bdd_deltail((*bts)(vars), bits*arlen(harity)));
	else vars = ae(bdd_deltail(vars, bits*arlen(harity)));
//	vars = ae(vars);
//	DBG(printbdd(wcout<<"ae:"<<endl, vars,vars_arity,hrel)<<endl;)
	return vars;
}

size_t arlen(const ints& ar) {
	size_t r = 0;
	for (auto x : ar) if (x > 0) r += x;
	return r;
}

