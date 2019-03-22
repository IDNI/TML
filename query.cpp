#include "query.h"
using namespace std;

size_t query::compute(size_t x, size_t v) {
	if (leaf(x) && v == nvars) return x;
	node n = getnode(x);
	if (leaf(x) || v+1 < n[0]) n = { v+1, x, x };
	if (s.find(v/bits+1) == s.end())
		return ++v, bdd_add({{v, compute(n[1], v), compute(n[2], v)}});
	if (e[v/bits] > 0)
		return compute(n[e[v/bits]&(1<<(bits-v%bits-1)) ? 1 : 2], v+1);
	if (e[v/bits] < 0)
		return	compute(path[(-e[v/bits]-1)*bits+v%bits] == 1 
			? n[1] : n[2], v + 1);
	size_t h;
	return	path[v] = 1, h = compute(n[1], v+1), path[v++] = -1,
		bdd_add({{v, h, compute(n[2], v)}});
}

set<size_t> query::get_s() const {
	set<size_t> r;
	for (size_t n=0; n!=e.size();++n)
		if (e[n]) r.insert(n+1), r.insert(abs(e[n]));
	return r;
}

query::query(size_t x, size_t bits, size_t ar, const std::vector<int_t>& e,
		int_t glt, int_t ggt, const std::vector<int_t>& excl)
	: bits(bits), nvars(ar*bits), e(e), glt(glt), ggt(ggt), excl(excl)
	, s(get_s()), path(nvars, 0) { 
	res = compute(x, 0);
}
