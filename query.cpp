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

query::query(size_t bits, const term& t, const std::vector<size_t>& perm) 
	: neg(t[0]<0), bits(bits), nvars((t.size()-1)*bits) , e(from_term(t))
	, perm(perm), s(get_s()), path(nvars, 0) {}

vector<int_t> query::from_term(const term& t) {
	vector<int_t> r(t.size()-1);
	map<int_t, int_t> m;
	auto it = m.end();
	for (int_t n = 1; n != (int_t)t.size(); ++n)
		if (t[n] >= 0) r[n-1] = t[n]+1;
		else if (m.end() == (it = m.find(t[n]))) m[t[n]] = -n;
		else r[n-1] = it->second;
	return r;
}

node flip(node n) {
	if (nleaf(n)) return n;
	if (n[1] == T) n[1] = F; else if (n[1] == F) n[1] = T;
	if (n[2] == T) n[2] = F; else if (n[2] == F) n[2] = T;
	return n;
}

size_t query::operator()(size_t x, size_t v) {
	if (leaf(x) && v == nvars) return x;
	node n = neg ? flip(getnode(x)) : getnode(x);
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (s.find(v/bits+1) == s.end())
		return bdd_ite(perm[v], (*this)(n[1],v+1), (*this)(n[2],v+1));
	if (e[v/bits] > 0)
		return (*this)(n[(e[v/bits]-1)&(1<<(bits-v%bits-1))?1:2], v+1);
	if (e[v/bits] < 0)
		return (*this)(n[path[(-e[v/bits]-1)*bits+v%bits]==1?1:2],v+1);
	return	path[v] = 1, x = (*this)(n[1], v+1), path[v] = -1,
		bdd_ite(perm[v], x, (*this)(n[2], v+1));
}

set<size_t> query::get_s() const {
	set<size_t> r;
	for (size_t n=0; n!=e.size();++n)
		if (e[n]) r.insert(n+1), r.insert(abs(e[n]));
	return r;
}

extents::extents(size_t bits, size_t ar, size_t tail, int_t glt, int_t ggt,
	const std::vector<int_t>& excl, const std::vector<int_t>& lt,
	const std::vector<int_t>& gt)
	: bits(bits), nvars(ar*bits), tail(tail), glt(glt), ggt(ggt)
	, excl(excl), lt(lt), gt(gt), path(nvars, 0) {}

int_t extents::get_int(size_t v) const {
	int_t r = 0, pos = v / bits, n = pos * bits;
	v %= bits;
	for (;n!=(int_t)((pos+1)*bits-v);++n) if (path[n]==1) r |= 1<<(n%bits);
	return r;
}

size_t extents::operator()(size_t x, size_t v) {
	if (leaf(x) && v == nvars) return x;
	node n = getnode(x);
//	if (!leaf(x) && n[0] <= tail)
//		return bdd_add({{n[0], (*this)(n[1], n[0]-1),
//			(*this)(n[2], n[0]-1)}});
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (s.find(v/bits+1) == s.end())
		return ++v, bdd_add({{v, (*this)(n[1], v), (*this)(n[2], v)}});
	int_t i = get_int(v);
	if (	(glt && i >= glt) ||
		(ggt && i <= ggt) ||
		(!(v % bits) && (
			binary_search(excl.begin(), excl.end(), i) ||
			(lt[v/bits] < 0 && get_int(-lt[v/bits]*bits) <= i) ||
			(lt[v/bits] > 0 && lt[v/bits] <= i) ||
			(gt[v/bits] < 0 && get_int(-gt[v/bits]*bits) >= i) ||
			(gt[v/bits] > 0 && gt[v/bits] >= i)
		)))
		return F;
	size_t y;
	path[v]=true, x=(*this)(n[1], v+1), path[v++]=false, y=(*this)(n[2], v);
	return v > tail ? x == F && y == F ? F : T : bdd_add({{v, x, y}});
}
