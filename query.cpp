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

query::query(size_t bits, const term& t, const sizes& perm, bool neg) 
	: bits(bits), nvars(t.args.size()*bits), e(from_term(t)), perm(perm)
	, domain(getdom()), path(nvars, 0), neg(neg) {}

#define flip(n) nleaf(n) ? (n) : \
	node{{ n[0], n[1]==T?F:n[1]==F?T:n[1], n[2]==T?F:n[2]==F?T:n[2] }}

size_t query::operator()(size_t x) {
//	DBG(out(wcout<<L"called with ", getnode(x)) << endl;)
	unordered_map<size_t, size_t> &m = neg ? negmemo : memo;
	auto it = m.find(x);
	if (it != m.end()) return it->second;
	return	m[x] = domain.size() ? compute(x, 0):
		bdd_permute(neg ? bdd_and_not(T, x) : x, perm);
}

size_t query::compute(size_t x, size_t v) {
	if (leaf(x) && (!trueleaf(x) || v == nvars)) return x;
	node n = neg&&!leaf(x) ? flip(getnode(x)) : getnode(x);
	if (!has(domain, v/bits+1))
		return bdd_ite(perm[v], compute(n[1],v+1), compute(n[2],v+1));
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (e[v/bits] > 0)
		return compute(n[(e[v/bits]-1)&(1<<(bits-v%bits-1))?1:2], v+1);
	if (e[v/bits] < 0)
		return compute(n[path[(-e[v/bits]-1)*bits+v%bits]==1?1:2],v+1);
	return	path[v] = 1, x = compute(n[1], v+1), path[v] = -1,
		bdd_ite(perm[v], x, compute(n[2], v+1));
}

sizes query::getdom() const {
	sizes r;
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n]) r.push_back(n+1), r.push_back(abs(e[n]));
	return sort(r);
}

bdd_and_eq::bdd_and_eq(size_t bits, const term& t)
	: bits(bits), nvars(t.args.size()*bits), e(from_term(t)) {}

size_t bdd_and_eq::operator()(size_t x) {
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	size_t r = x;
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n] > 0) 
			for (size_t k = 0; k != bits; ++k)
				r = bdd_and(r,
					from_bit(k,(e[n]-1)&(1<<(bits-k-1))));
		else if (e[n] < 0)
			for (size_t k = 0; k != bits; ++k)
				r = bdd_and(r,
					from_eq(n*bits+k, bits*(-e[n]-1)+k));
	return memo[x] = r;
}

builtin_res leq_const::operator()(const vector<char>& path, size_t from,
	size_t to) const {
	bool bit;
	for (size_t n = from; n != to; ++n)
		switch (bit = (c & (1<<(bits-n%bits-1))), path[n]) {
			case 0: return bit ? CONTBOTH : CONTLO;
			case 1: if (!bit) return FAIL; break;
			default:if (bit) return PASS;
		}
	return to - from == bits ? PASS : CONTBOTH;
}

builtin_res geq_const::operator()(const vector<char>& path, size_t from,
	size_t to) const {
	bool bit;
	for (size_t n = from; n != to; ++n)
		switch (bit = (c & (1<<(bits-n%bits-1))), path[n]) {
			case 0: return bit ? CONTHI : CONTBOTH;
			case 1: if (!bit) return PASS; break;
			default:if (bit) return FAIL;
		}
	return to - from == bits ? PASS : CONTBOTH;
}
