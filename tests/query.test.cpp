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
#include <map>
using namespace std;
/*
size_t query_ref(size_t x, term t, size_t bits, vector<size_t>& perm) {
	size_t y = fact(t, bits), ar = t.size()-1, r;
	wcout << "x:"<<endl << from_bits(x, bits, ar);
	wcout << "y:"<<endl << from_bits(y, bits, ar);
	bools ex(ar*bits, 0);
	map<int_t, size_t> m;

	for (size_t i = 1; i < t.size(); ++i)
		if (t[i] < 0 && m.find(t[i]) == m.end()) m[t[i]]=i-1;
		else for (size_t b = 0; b < bits; ++b) ex[(i-1)*bits+b] = true;
	
	for (size_t n = 0; n < bits*ar; ++n)
		if (t[n/bits+1] < 0)
			perm.push_back((ar-1-m[t[n/bits+1]])*bits+n%bits);
		else perm.push_back(n);

	r = bdd_and(x, y);
	wcout << "and:" << endl << from_bits(r, bits, ar);
	r = bdd_ex(r, ex);
	wcout << "ex:" << endl << from_bits(r, bits, ar);
	r = bdd_permute(r, perm);
	wcout << "perm:"<<endl << from_bits(r, bits, ar);
	return r;
}
*/

void from_range(size_t max, size_t bits, size_t arg, size_t args, spnode r) {
	spnode x = F;
	for (size_t n = 0; n <= max; ++n)
		x = bdd_or(x, from_int(n, bits, arg, args));
	r = bdd_and(r, x);
}

void test_query() {
	size_t bits, arg1 = 0, arg2 = 1, args = 3;
	// D: this needs bitsmeta of some sort (table, alt or custom?)
	//bitsmeta bm;
	for (bits = 1; bits <= 10; ++bits)
		for (size_t n = 0; n != (size_t)(1<<bits); ++n) {
			wcout<<"max: "<<n<<" bits: "<<bits<<endl;
			builtins<leq_const> l1({arg1},bits,args,leq_const(n,bits,args));
			builtins<leq_const> l2({arg2},bits,args,leq_const(n,bits,args));
			spnode x = T, y = bdd_and(l1(T),l2(T));
			from_range(n, bits, arg1, args, x);
			from_range(n, bits, arg2, args, x);
			wcout<<"x:"<<endl<<allsat(x,bits*args)
				<<"y:"<<endl<<allsat(y,bits*args)<<endl;
			assert(x == y);
		}

/*	size_t bits = 3, x = F, ar, r, f;
	matrix m;
	//m.push_back({ 1, 1, 2, 3});
	m.push_back({ 1, 2, 3, 4});
	m.push_back({ 1, 2, 2, 3});
	m.push_back({ 1, 3, 2, 3});
	ar = m[0].size()-1;
	for (term t : m) x = bdd_or(x, fact(t, bits));
	vector<size_t> perm;
	f = query_ref(x,  { 1, 2, -1, -2 }, bits, perm);
	query q(bits, { 1, 2, -1, -2 }, perm);
	r = q(x);
	wcout << "f:"<<endl << from_bits(f, bits, ar);
	wcout << "q:"<<endl << from_bits(r, bits, ar);
	assert(r == f);
	perm.clear();
	f = query_ref(x,  { 1, -1, -1, -2 }, bits, perm);
	query q1(bits, { 1, -1, -1, -2 }, perm);
	r = q(x);
	assert(q1(x) == f);
	m.push_back({ 1, 5, 3, 2});
	for (term t : m) x = bdd_or(x, fact(t, bits));
	extents e(bits, ar, bits*(ar-0), {0,1,2,3}, 6, 0, {0,0,0}, 
		{0,0,0}, {0,0,-2}, {0,0,0}, {0,1,0});
	wcout << "x:"<<endl << from_bits(x, bits, ar)<<endl;
	wcout << "e:"<<endl << from_bits(e(x), bits, ar)<<endl;
	exit(0);
//	assert(q(x) = bdd_or(term(m[1],bits), term(m[2],bits),ex)
	for(size_t k=0; k!=100;++k) {
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
