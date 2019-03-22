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
#include "rule.h"
using namespace std;

size_t query_ref(size_t x, term t, size_t bits, vector<size_t> perm) {
	size_t y = fact(t, bits), ar = t.size()-1, r;
	wcout << "x:"<<endl << from_bits(x, bits, ar);
	wcout << "y:"<<endl << from_bits(y, bits, ar);
	bools ex(ar*bits, 0);
	set<int_t> s;

	for (size_t i = 1; i < t.size(); ++i)
		if (t[i] < 0 && s.find(t[i]) == s.end()) s.insert(t[i]);
		else for (size_t b = 0; b < bits; ++b) ex[(i-1)*bits+b] = true;

	r = bdd_and(x, y);
	wcout << "and:" << endl << from_bits(r, bits, ar);
	r = bdd_ex(r, ex);
	wcout << "ex:" << endl << from_bits(r, bits, ar);
	r = bdd_permute(r, perm);
	wcout << "perm:"<<endl << from_bits(r, bits, ar);
	return r;
}

void test_query() {
	size_t bits = 3, x = F, ar, r;
	matrix m;
	m.push_back({ 1, 1, 2, 3});
	m.push_back({ 1, 2, 3, 4});
	m.push_back({ 1, 2, 2, 3});
	m.push_back({ 1, 3, 2, 3});
	ar = m[0].size()-1;
	for (term t : m) x = bdd_or(x, fact(t, bits));
	vector<size_t> perm;
	for (size_t n = 0; n < bits*ar; ++n) perm.push_back(n);
	query q(bits, { 1, 2, -1, -2 }, perm);
	r = q(x);
	wcout << "q:"<<endl << from_bits(r, bits, ar);
	assert(r == query_ref(x,  { 1, 2, -1, -2 }, bits, perm));
//	assert(q(x) = bdd_or(term(m[1],bits), term(m[2],bits),ex)
/*	for(size_t k=0; k!=100;++k) {
		wcout << k << endl;
		size_t bits = 3, ar = 10;
		tt t = rndtt(bits * ar, 1000);
	//	wcout << t << endl;
		size_t x = t.bdd(), y = x;
		for (size_t n = 0; n < bits; ++n)
			y = bdd_and(y, from_eq(n, bits*3+n)),
			y = bdd_and(y, from_eq(n + bits, bits*5+n));
		bools b(bits * ar, 0);
		for (size_t n = 0; n < bits; ++n)
			b[bits*2+n]=b[bits*3+n]=b[bits*5+n]=true;
		y=bdd_ex(bdd_and(y,from_int(2,bits,2*bits)),b);
		vector<size_t> perm;
		for (size_t n = 0; n < bits*ar; ++n) perm.push_back(n+1);
		assert(query(false,bits,ar,{ 0, 0, 2, -1, 0, -2 },perm)(x)==y);
	}*/
}
