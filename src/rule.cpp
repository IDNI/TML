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

size_t fact(const term& v, range& rng) {
	//DBG(wcout<<"add fact:"<<v<<endl;)
	if (v.arity() == ints{0}) return T;
	size_t r = T;
	rule::varmap m;
	for (size_t j = 0; j != v.nargs(); ++j)
		if (v.arg(j) < 0) m.emplace(v.arg(j), j);
	//DBG(printbdd(wcout<<"ret1:"<<endl, r, v.arity, v.rel)<<endl;)
	if (!m.empty()) {
//		DBG(printbdd(wcout<<"ret2:"<<endl, r, v.arity, v.rel)<<endl;)
		for (size_t j = 0; j != v.nargs(); ++j)
			if (v.arg(j) >= 0 || j == m[v.arg(j)]) continue;
			else for (size_t b = 0; b != rng.bits; ++b)
				r = bdd_and(r, from_eq(
					POS(b,rng.bits,j,v.nargs()),
					POS(b,rng.bits,m[v.arg(j)],v.nargs())));
//		DBG(printbdd(wcout<<"ret3:"<<endl, r, v.arity, v.rel)<<endl;)
	}
	for (size_t j = 0; j != v.nargs(); ++j)
		if (v.arg(j) >= 0)
			from_int_and(v.arg(j), rng.bits, j, v.nargs(), r);
	if (v.neg()) r = bdd_and_not(T, r);
	if (!m.empty()) {
		sizes domain;
		for (auto x : m) domain.push_back(x.second);
		r = bdd_and(r, rng(domain, v.nargs()));
//		DBG(bdd_out(wcout, r)<<endl;)
	}
//	DBG(printbdd(wcout<<"ret:"<<endl, r, rng.bits, v.arity(), v.rel())<<endl;)
//	DBG(bdd_out(wcout, r)<<endl;)
//	DBG(wcout<<allsat(r, rng.bits*v.nargs())<<endl;)
//	DBG(printbdd(wcout<<"dt:"<<endl, bdd_deltail(r, v.args.size(),
//		v.args.size()-2, bits), ints{v.args.size()-2}, v.rel)<<endl;)
	return r;
}

sizes rule::get_perm(const term& b, varmap& m) {
	sizes perm(rng.bits * b.nargs());
	auto it = m.end();
	for (size_t j = 0; j != perm.size(); ++j) perm[j] = j;
	for (size_t k = 0; k != b.nargs(); ++k) {
		if (b.arg(k) >= 0) continue;
		it = m.emplace(b.arg(k), maxhlen + m.size()).first;
		for (size_t j = 0; j != rng.bits; ++j)
			perm[POS(j, rng.bits, k, b.nargs())] =
				POS(j, rng.bits, it->second, nvars+maxhlen);
	}
	return perm;
}

rule::rule(matrix h, matrix b, const vector<size_t*>& dbs, range& rng) :
	dbs(dbs), rng(rng) {
	//DBG(wcout<<"h:"<<endl<<h<<endl<<"b:"<<endl<<b<<endl;)
	hperm.resize(h.size()), hpref.resize(h.size()), neg.resize(h.size()),
	maxhlen = 0;
	for (const term& t : h) maxhlen = max(maxhlen, t.nargs());
	set<int_t> vs;
	for (const term& t : b) for (int_t i : t.args()) if (i<0) vs.insert(i);
	for (const term& t : h) for (int_t i : t.args()) if (i<0) vs.insert(i);
	nvars = vs.size(), vs.clear();
	for (size_t n = 0; n != h.size(); ++n) {
		hperm[n].resize(rng.bits * (maxhlen + nvars));
		for (size_t j = 0; j != hperm[n].size(); ++j) hperm[n][j] = j;
		hpref[n] = h[n].pref(), neg[n] = h[n].neg();
		ae.emplace_back(rng.bits, h[n], false);
	}
	varmap m;
	for (size_t n = 0; n != b.size(); ++n)
		q.emplace_back(
			rng.bits, b[n], get_perm(b[n], m),b[n].neg());
	for (size_t n = 0; n != h.size(); ++n)
		for (size_t k = 0; k != h[n].nargs(); ++k)
			if (h[n].arg(k) < 0)
				for (size_t j = 0; j != rng.bits; ++j)
					hperm[n][POS(j, rng.bits,m[h[n].arg(k)],
						nvars+maxhlen)]=POS(j, rng.bits,
						k, nvars+maxhlen);
	get_ranges(h, b, m);
}

void rule::get_ranges(const matrix& h, const matrix& b, const varmap& m) {
	hleq = sizes(h.size(), T), bleq = T;
	set<int_t> bnegvars, bposvars, hposvars, del;
	sizes domain;
	for (const term& t : b)
		for (int_t i : t.args())
			if (i < 0) (t.neg() ? bnegvars : bposvars).insert(i);
	for (size_t n = 0; n != h.size(); ++n) {
		for (size_t k = 0; k != h[n].nargs(); ++k)
			if (h[n].arg(k) < 0 && !has(bnegvars, h[n].arg(k)) &&
				!has(bposvars, h[n].arg(k)))
				domain.push_back(k);
		hleq[n] = rng(domain, h[n].nargs());
	//	if (domain.size())for(auto t:h)DBG(drv->print_term(wcout,t));
//		for (size_t i : domain)
//			hleq[n] = bdd_and(hleq[n],builtins<leq_const>({i},bits,
//				h[n].nargs(),
//				leq_const(dsz-1, bits, h[n].nargs()))(T));
		domain.clear();
	}
	for (const term& t : h)
		if (!t.neg())
			for (int_t i : t.args())
				if (i < 0) hposvars.insert(i);
	for (int_t i : bposvars) bnegvars.erase(i);
	for (int_t i : bnegvars) if (!has(hposvars, i)) del.insert(i);
	for (int_t i : del) bnegvars.erase(i);
	for (int_t i : bnegvars) domain.push_back(m.at(i));
	bleq = rng(domain, maxhlen + nvars);
//	if (!domain.empty())
//		bleq=bdd_and(bleq,builtins<leq_const>(domain,bits,maxhlen+nvars,
//			leq_const(dsz-1, bits, maxhlen+nvars))(T));
}

sizes rule::fwd() {
	sizes r(hpref.size()), v(q.size());
	size_t vars;
	for (size_t n = 0; n < q.size(); ++n)
		if (F == (v[n] = q[n](*dbs[n]))) return {};
//		DBG(else printbdd(wcout<<"q"<<n<<endl,v[n],rng.bits,
//			ints{(int_t)(maxhlen+nvars)}, hrel[0])<<endl<<"---"<<endl;)
	v.push_back(bleq);
	if (F == (vars = bdd_and_many(move(v)))) return {};
//	DBG(printbdd(wcout<<"q:"<<endl,vars,rng.bits,
//		ints{(int_t)(maxhlen+nvars)}, hrel[0])<<endl<<"---"<<endl;)
	for (size_t k = 0; k != r.size(); ++k) {
		r[k] = bdd_permute(vars, hperm[k]);
		//DBG(printbdd(wcout<<"perm:"<<endl,r[k],
		//		ints{(int_t)(maxhlen+nvars)},hrel[k])<<endl;)
		//DBG(printbdd(wcout<<"perm:"<<endl,r[k],harity[k],hrel[k])<<endl;)
//		DBG(bdd_out(wcout, r[k])<<endl;)
//		DBG(printbdd(wcout<<"bleq:"<<endl,r[k],harity[k],hrel[k])<<endl;)
		r[k]=bdd_deltail(r[k], maxhlen+nvars, hpref[k].len(), rng.bits);
		//DBG(printbdd(wcout<<"dt:"<<endl,r[k],rng.bits,harity[k],hrel[k])<<endl;)
		//DBG(bdd_out(wcout, r[k])<<endl;)
		r[k] = ae[k](r[k]);
		//DBG(printbdd(wcout<<"ae:"<<endl,r[k],rng.bits,harity[k],hrel[k])<<endl;)
		r[k] = bdd_and(hleq[k], r[k]);
		//DBG(printbdd(wcout<<"hleq:"<<endl,r[k],rng.bits,harity[k],hrel[k])<<endl;)
	}
	return r;
}
