#include "query.h"
using namespace std;

size_t bdd_eq_ex::compute(size_t x, size_t v) {
	if (leaf(x) && v == nvars) return x;
	node n = getnode(x);
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (s.find(v/bits+1) == s.end())
		return ++v, bdd_add({{v, compute(n[1],v),compute(n[2],v)}});
	if (e[v/bits])
		return	compute(path[(e[v/bits]-1)*bits+v%bits] == 1 
			? n[1] : n[2], v + 1);
	size_t h;
	return	path[v] = 1, h = compute(n[1], v+1), path[v++] = -1,
		bdd_add({{v, h, compute(n[2], v)}});
}

set<size_t> bdd_eq_ex::get_s() const {
	set<size_t> r;
	for (size_t n=0; n!=e.size();++n) if (e[n])r.insert(n+1),r.insert(e[n]);
	return r;
}

bdd_eq_ex::bdd_eq_ex(size_t x, size_t bits, size_t ar, const vector<size_t>& e)
	: bits(bits), nvars(ar*bits), e(e), s(get_s()), path(nvars, 0) { 
	res = compute(x, 0);
}
