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
#include "tables.h"
using namespace std;

// conjunctive query containment
// following Ullman's "Information Integration using Logical Views"
// https://www.sciencedirect.com/science/article/pii/S0304397599002194

int_t rep(int_t x, const env& m) {
	if (x >= 0) return x;
	auto it = m.find(x);
	return it == m.end() ? x : rep(it->second, m);
}

bool rep(int_t x, int_t y, env& m) {
	if ((x = rep(x, m)) == (y = rep(y, m))) return true;
	if (x >= 0 && y >= 0) return false;
	if (y < x) swap(x, y);
	return m.emplace(x, y), true;
}

bool unify(const term& x, const term& y, env& m) {
	if (x.tab != y.tab || x.neg != y.neg) return false;
	assert(x.size() == y.size());
	for (size_t n = 0; n != x.size(); ++n)
		if (!rep(x[n], y[n], m)) return false;
	return true;
}

void sub(term& x, const env& m) { for (int_t& i : x) i = rep(i, m); }
void sub(vector<term>& v, const env& m) { for (term& t : v) sub(t, m); }
term sub1(term x, const env& m) { return sub(x, m), x; }
vector<term> sub1(vector<term> v, const env& m) { return sub(v, m), v; }

bool derives(const term& t, term h, vector<term> b, const vector<term>& kb,
	env& e, size_t n = 0) {
	env v;
	if (n == b.size()) return unify(t, h, v);
	for (const term& x : kb)
		if (	unify(b[n], x, v = e) &&
			derives(t, sub1(h, v), sub1(b, v), kb, v, n + 1))
				return e = v, true;
	return false;
}

// whether 1 is contained in 2, i.e. returns no more results than 2
//map<int_t, int_t> cqc(term h1, vector<term> b1, term h2, vector<term> b2) {
//	env f = freeze(h1, b1), e;
//	return derives(h1, h2, b2, b1, e) ? e : map<int_t, int_t>();
//}

wostream& operator<<(wostream& os, const env& e) {
	for (auto x : e) o::out() << x.first << " = " << x.second << endl;
	return os;
}

void set(term& t, const ints& i) {
	t.clear();
	for (int_t x : i) t.push_back(x);
}

/*int main() {
	term x1, x2, x3, y1, y2, y3;
	::set(x1, { -1, -2 }), ::set(x2, { 1, -3 }), ::set(x3, { -3, -2 }),
	::set(y1, { -5, -2 }), ::set(y2, { -1, -3 }), ::set(y3, { -4, -2 });
	x1.tab = x2.tab = x3.tab = y1.tab = y2.tab = y3.tab = 1;
	o::out() << cqc(x1, {x2, x3}, y1, {y2, y3});
	return 0;

}*/
