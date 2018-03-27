#include <map>
#include <set>
#include <cstring>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <alloca.h>
using namespace std;

typedef int32_t int_t;
typedef int_t* tup;
typedef int_t* pat;
typedef int_t* mat; // env
const size_t max_ar = 256;

mat unify(const pat _p, size_t nvars, tup t, size_t ar) {
	size_t sz1 = nvars * sizeof(int_t), sz2 = ar * sizeof(int_t);
	mat r = (mat)memset(alloca(sz1), 0, sz1);
	pat p = (pat)memcpy(alloca(sz2), _p, sz2);
	for (size_t n = 0; n < ar; ++n) {
		while (p[n] < 0) {
			if (r[abs(p[n])-1]) p[n] = r[abs(p[n])-1];
			else p[n] = r[abs(p[n])-1] = t[n];
		}
		if (t[n] != p[n]) return 0;
	}
	return (mat)memcpy(new int_t[nvars], r, sz1);
}

void f(const pat* p, size_t np, const tup t, size_t ar, size_t nvars, map<pat, set<mat>> &r) {
	for (size_t n = 0; n < np; ++n)
		if (mat m = unify(p[n], nvars, t, ar); m) r[p[n]].emplace(m);
}

int main(int, char**) {
	int_t a = 1, b = 2, c = 3, vx = -1, vy = -2;
	int_t p1[] = { a, vx, vy };
	int_t p2[] = { vx, vy, a };
	int_t x[] = { a,  b,  c };
	int_t y[] = { a,  c,  a };
	int_t z[] = { b,  c,  a };
	pat p[] = {p1, p2};
	map<pat, set<mat>> m;
	f(p, 2, x, 3, 2, m);
	f(p, 2, y, 3, 2, m);
	f(p, 2, z, 3, 2, m);
	for (auto t : m) {
		for (size_t n = 0; n < 3; ++n) cout << t.first[n] << ' ';
		cout << " =>" << endl;
		for (auto s : t.second) {
			for (size_t n = 0; n < 2; ++n) cout << s[n] << ' ';
			cout << endl;
		}
	}
	return 0;
}
