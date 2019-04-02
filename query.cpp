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
#include "query.h"
#ifdef DEBUG
#include "lp.h"
#endif
#include <map>
#include <algorithm>
using namespace std;

template<typename T> T sort(const T& x){T t=x;return sort(t.begin(),t.end()),t;}

ints from_term(const term& t) {
	ints r(t.args.size(), 0);
	for (int_t n = 0, k; n != (int_t)t.args.size(); ++n)
		if (t.args[n] >= 0) r[n] = t.args[n]+1;
		else if ((k = n))
			while (k--)
				if (t.args[k] == t.args[n]) {
					r[n] = -k-1;
					break;
				}
	return r;
}

bools get_ex(const term& t, size_t bits) {
	bools ex(t.args.size()*bits, false);
	ints r(t.args.size(), 0);
	for (int_t n = 0, k; n != (int_t)t.args.size(); ++n)
		if (t.args[n] >= 0) r[n] = t.args[n]+1;
		else if ((k = n))
			while (k--)
				if (t.args[k] == t.args[n]) {
					r[n] = -k-1;
					break;
				}
	for (size_t n = 0; n != r.size(); ++n)
		if (r[n])
			for (size_t k = 0; k != bits; ++k)
				ex[POS(k, bits, n, r.size())] = true;
	return ex;
}


query::query(size_t bits, const term& t, const sizes& perm, bool neg) 
	: ex(get_ex(t, bits)), neg(neg), perm(perm), ae(bits, t, neg) {}

#define flip(n) nleaf(n) ? (n) : \
	node{{ n[0], n[1]==T?F:n[1]==F?T:n[1], n[2]==T?F:n[2]==F?T:n[2] }}

size_t query::operator()(size_t x) {
//	DBG(out(wcout<<L"called with ", getnode(x)) << endl;)
	unordered_map<size_t, size_t> &m = neg ? negmemo : memo;
	auto it = m.find(x);
	if (it != m.end()) return it->second;
	return m[x] = bdd_permute(bdd_ex(ae(x), ex), perm);
	//return m[x] = domain.size() ? compute(x, 0):
	//	bdd_permute(neg ? bdd_and_not(T, x) : x, perm);
}

/*size_t query::compute(size_t x, size_t v) {
	if (leaf(x) && (!trueleaf(x) || v == nvars)) return x;
	node n = neg&&!leaf(x) ? flip(getnode(x)) : getnode(x);
	const size_t arg = ARG(v, e.size());
	if (!has(domain, arg+1))
		return bdd_ite(perm[v], compute(n[1],v+1), compute(n[2],v+1));
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (e[arg] > 0)
		return compute(n[(e[arg]-1)&(1<<BIT(v,e.size(),bits))?1:2],v+1);
	if (e[arg] < 0) {
		if (path[POS(BIT(v,e.size(),bits),bits,-e[arg]-1,e.size())]==1)
			return path[v] = 1, compute(n[1],v+1);
		return path[v] = -1, compute(n[2],v+1);
	}
	return	path[v] = 1, x = compute(n[1], v+1), path[v] = -1,
		bdd_ite(perm[v], x, compute(n[2], v+1));
}*/

/*sizes query::getdom() const {
	sizes r;
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n]) r.push_back(n+1), r.push_back(abs(e[n]));
	return sort(r);
}*/

bdd_and_eq::bdd_and_eq(size_t bits, const term& t, const bool neg)
	: bits(bits), nvars(t.args.size()*bits), e(from_term(t)), neg(neg)
	{DBG(_t=t;) }

size_t bdd_and_eq::operator()(const size_t x) {
	unordered_map<size_t, size_t> &m = neg ? negmemo : memo;
	auto it = m.find(x);
	if (it != m.end()) return it->second;
	vector<size_t> v = {x};
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n] > 0) 
			v.push_back(from_int(e[n]-1, bits, n, e.size()));
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n] < 0)
			for (size_t k = 0; k != bits; ++k)
				v.push_back(from_eq(POS(k, bits, n, e.size()),
					POS(k, bits, -e[n]-1, e.size())));
	if (neg) {
		if (v.size() == 1) return m[x] = bdd_and_not(T, v[0]);
		v.push_back(bdd_and_not(v[1], v[0])),
		v.erase(v.begin(), v.begin()+1);
	}
	return m[x] = bdd_and_many(v);
}

builtin_res leq_const::operator()(const bools& path, size_t arg, size_t v)const{
	return	path[v] ? (c&(1<<(BIT(v,args,bits)))) ? 
		v == POS(0, bits, arg, args) ? PASS : CONTBOTH : FAIL :
		(c&(1<<(BIT(v,args,bits)))) ||
		v == POS(0, bits, arg, args)	? PASS : CONTBOTH;
}

builtin_res geq_const::operator()(const vector<char>& path, size_t arg,
	size_t v) const {
	bool bit;
	size_t n = POS(bits-1, bits, arg, args);
	for (; n <= POS(0, bits, arg+1, args); n += args)
		switch (bit = (c & (1<<BIT(n,args,bits))), path[n]) {
			case 0: return bit ? CONTHI : CONTBOTH;
			case 1: if (!bit) return PASS; break;
			default:if (bit) return FAIL;
		}
	return v == args*bits ? PASS : CONTBOTH;
}
