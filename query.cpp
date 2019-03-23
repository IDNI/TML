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
#include <map>
#include <algorithm>
using namespace std;

template<typename T> T sort(const T& x){T t=x;return sort(t.begin(),t.end()),t;}
#define has(x, y) binary_search(x.begin(), x.end(), y)

vector<int_t> from_term(const term& t) {
	vector<int_t> r(t.size()-1);
	map<int_t, int_t> m;
	auto it = m.end();
	for (int_t n = 1; n != (int_t)t.size(); ++n)
		if (t[n] >= 0) r[n-1] = t[n]+1;
		else if (m.end() == (it = m.find(t[n]))) m[t[n]] = -n-1;
		else r[n-1] = it->second;
	return r;
}

query::query(size_t bits, const term& t, const sizes& perm) 
	: neg(t[0]<0), bits(bits), nvars((t.size()-1)*bits), e(from_term(t))
	, perm(perm), domain(getdom()), path(nvars, 0) {}

node flip(node n) {
	if (nleaf(n)) return n;
	if (n[1] == T) n[1] = F; else if (n[1] == F) n[1] = T;
	if (n[2] == T) n[2] = F; else if (n[2] == F) n[2] = T;
	return n;
}

size_t query::operator()(size_t x, size_t v) {
	if (leaf(x) && (!trueleaf(x) || v == nvars)) return x;
	node n = neg ? flip(getnode(x)) : getnode(x);
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (!has(domain, v/bits+1))
		return bdd_ite(perm[v], (*this)(n[1],v+1), (*this)(n[2],v+1));
	if (e[v/bits] > 0)
		return (*this)(n[(e[v/bits]-1)&(1<<(bits-v%bits-1))?1:2], v+1);
	if (e[v/bits] < 0)
		return (*this)(n[path[(-e[v/bits]-1)*bits+v%bits]==1?1:2],v+1);
	return	path[v] = 1, x = (*this)(n[1], v+1), path[v] = -1,
		bdd_ite(perm[v], x, (*this)(n[2], v+1));
}

sizes query::getdom() const {
	sizes r;
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n]) r.push_back(n+1), r.push_back(abs(e[n]));
	return sort(r);
}

bdd_and_eq::bdd_and_eq(size_t bits, const term& t)
	: bits(bits), nvars((t.size()-1)*bits), e(from_term(t))
	, domain(getdom()), path(nvars, 0) {}

sizes bdd_and_eq::getdom() const {
	sizes r;
	for (size_t n = 0; n != e.size(); ++n)
		if (e[n]) r.push_back(n+1), r.push_back(abs(e[n]));
	return sort(r);
}

size_t bdd_and_eq::operator()(size_t x, size_t v) {
	if (leaf(x) && (!trueleaf(x) || v == nvars)) return x;
	node n = getnode(x);
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (!has(domain, v/bits+1))
		return ++v, bdd_add({{v, (*this)(n[1], v), (*this)(n[2], v)}});
	if (e[v/bits] > 0)
		return	(e[v / bits] - 1) & (1 << (bits - v % bits - 1))
			? bdd_add({{v+1, (*this)(n[1], v+1), F}})
			: bdd_add({{v+1, F, (*this)(n[2], v+1)}});
	if (e[v/bits] < 0)
		return	path[(-e[v / bits] - 1) * bits + v % bits] == 1
			? bdd_add({{v+1, (*this)(n[1], v+1), F}})
			: bdd_add({{v+1, F, (*this)(n[2], v+1)}});
	return	path[v] = 1, x = (*this)(n[1], v+1), path[v++] = -1,
		bdd_add({{v, x, (*this)(n[2], v)}});
}

extents::extents(size_t bits, size_t ar, size_t tail, const sizes& domain,
	int_t glt, int_t ggt, const term& excl, const term& lt, const term& gt,
	const sizes& succ, const sizes& pred) : bits(bits), nvars(ar*bits)
	, tail(tail), glt(glt), ggt(ggt), excl(sort(excl)), lt(lt), gt(gt)
	, succ(succ), pred(pred) , domain(sort(domain)), path(nvars, 0) {}

int_t extents::get_int(size_t v) const {
	int_t r = 0, pos = (v-1) / bits, n = pos * bits;
	for (;n!=(int_t)((pos+1)*bits);++n)
		if (path[n]==1) r |= 1<<(bits-1-n%bits);
	return r;
}

size_t extents::operator()(size_t x, size_t v) {
	if (leaf(x) && (!trueleaf(x) || v == nvars+1)) return x;
	node n = getnode(x);
	int_t i;
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	assert(v <= nvars);
	if (!has(domain, v/bits+1))
		return ++v, bdd_add({{v, (*this)(n[1], v), (*this)(n[2], v)}});
	if (v < bits || ((v) % bits)) goto cont;
	i = get_int(v);
	if (	(glt && i >= glt) ||
		(ggt && i <= ggt) ||
		has(excl, i) ||
		(gt[v/bits-1] < 0 && i <= get_int(bits*-gt[v/bits-1])) ||
		(gt[v/bits-1] > 0 && i <= gt[v/bits-1]) ||
		(lt[v/bits-1] < 0 && i >= get_int(bits*-lt[v/bits-1])) ||
		(lt[v/bits-1] > 0 && i >= lt[v/bits-1]) ||
		(succ[v/bits-1] && i != 1+get_int(bits*succ[v/bits-1])) ||
		(pred[v/bits-1] && i+1 != get_int(bits*pred[v/bits-1])))
		return F;
cont:	size_t y;
	path[v]=true, x=(*this)(n[1], v+1), path[v++]=false, y=(*this)(n[2], v);
	return v > tail ? x == F && y == F ? F : T : bdd_add({{v, x, y}});
}
