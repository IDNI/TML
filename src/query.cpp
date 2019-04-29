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

ints from_term(const term& t) {
	ints r(t.nargs(), 0);
	for (int_t n = 0, k; n != (int_t)t.nargs(); ++n)
		if (t.arg(n) >= 0) r[n] = t.args()[n]+1;
		else if ((k = n))
			while (k--)
				if (t.arg(k) == t.arg(n)) {
					r[n] = -k-1;
					break;
				}
	return r;
}

bools get_ex(const term& t, size_t bits) {
	bools ex(t.nargs()*bits, false);
	ints r(t.nargs(), 0);
	for (int_t n = 0, k; n != (int_t)t.nargs(); ++n)
		if (t.arg(n) >= 0) r[n] = t.arg(n)+1;
		else if ((k = n))
			while (k--)
				if (t.arg(k) == t.arg(n)) {
					r[n] = -k-1;
					break;
				}
	for (size_t n = 0; n != r.size(); ++n)
		if (r[n])
			for (size_t k = 0; k != bits; ++k)
				ex[POS(k, bits, n, r.size())] = true;
	return ex;
}

query::query(size_t bits, const term& t, const sizes& perm, bool neg) :
	ex(get_ex(t, bits)), neg(neg), perm(perm), ae(bits, t, neg) {
		DBG(_t = t;)
/*		auto it = memos.find(k);
		if (it != memos.end()) m = it->second;
		m = memos[k] = new unordered_map<size_t, size_t>;*/
	}

#define flip(n) nleaf(n) ? (n) : \
	bdd{{ n[0], n[1]==T?F:n[1]==F?T:n[1], n[2]==T?F:n[2]==F?T:n[2] }}

spbdd query::operator()(spbdd x) {
//	DBG(out(wcout<<L"called with ", getbdd(x)) << endl;)
	//return (ae(x) / ex) ^ perm;
	return bdd_permute_ex(ae(x, T), ex, perm);
/*	x = ae(x);
	auto it = m->find(x);
	if (it != m->end()) return it->second;
	return ++::memos, m->emplace(
		x, bdd_permute(bdd_ex(ae(x),k.ex), k.perm)).first->second;*/
	//return m[x] = domain.size() ? compute(x, 0):
	//	bdd_permute(neg ? bdd_and_not(T, x) : x, perm);
}

bdd_and_eq::bdd_and_eq(size_t bits, const term& t, const bool neg) :
	k(bits, t.nargs()*bits, from_term(t), neg), m(memos[k]) {
	DBG(_t=t;)
	bdds v;
	for (size_t n = 0; n != k.e.size(); ++n)
		if (k.e[n] > 0) 
			v.push_back(from_int(k.e[n]-1, k.bits, n, k.e.size()));
	for (size_t n = 0; n != k.e.size(); ++n)
		if (k.e[n] < 0)
			for (size_t i = 0; i != k.bits; ++i)
				v.push_back(bdd::from_eq(
					POS(i, k.bits,n,k.e.size()),
					POS(i, k.bits, -k.e[n]-1, k.e.size())));
	z = bdd_and_many(move(v));
	DBG(assert_nvars(z, bits * t.nargs());)
}

spbdd bdd_and_eq::operator()(const spbdd x, const spbdd y) {
	auto it = m.find(x);
	if (it != m.end()) return it->second;
	return onmemo(), m.emplace(x, bdd_and_many({x,y,z})).first->second;
}

/*builtin_res geq_const::operator()(const vector<char>& path, size_t arg,
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
}*/

//#define get_leq(c) builtins<leq_const>(arg,bits,args,leq_const(c,bits,args))(T)
#define get_leq(c) c->second(T)
#define get2(b1, b2) (bdd::from_bit(POS(0,bits,arg,args), b1) && \
		bdd::from_bit(POS(1,bits,arg,args), b2))
#define ischar get2(true, false)
#define isnum get2(false, true)
#define issym get2(false, false)
#define chars_clause bdd_impl(ischar, get_leq(ct))
#define nums_clause bdd_impl(isnum, get_leq(nt))
#define syms_clause bdd_impl(issym, get_leq(st))
#define notchar (T%ischar)
#define notnum (T%isnum)
#define notsym (T%issym)

spbdd range::operator()(size_t arg, size_t args) {
	auto it = memo.find({syms,nums,chars,(int_t)args,(int_t)arg});
	if (it != memo.end()) return it->second;
	auto st = bsyms.find({arg, args, syms});
	if (st == bsyms.end())
		st = bsyms.emplace(key{arg, args, syms},
			builtins<leq_const>(arg,bits,args,
			leq_const(((syms-1)<<2)|3,bits,args))).first;
	auto nt = bnums.find({arg, args, nums});
	if (nt == bnums.end())
		nt = bnums.emplace(key{arg, args, nums},
			builtins<leq_const>(arg,bits,args,
			leq_const(((nums-1)<<2)|3,bits,args))).first;
	auto ct = bchars.find({arg, args, chars});
	if (ct == bchars.end())
		ct = bchars.emplace(key{arg, args, chars},
			builtins<leq_const>(arg,bits,args,
			leq_const(((chars-1)<<2)|3,bits,args))).first;
	bdds v = {
		ischar || isnum || issym,
		chars ? chars_clause : notchar,
		nums ? nums_clause : notnum,
		syms ? syms_clause : notsym};
	spbdd r = bdd_and_many(v);
	return onmemo(), memo[{syms,nums,chars,(int_t)args,(int_t)arg}] = r;
}
unordered_map<array<int_t, 5>, spbdd, array_hash<int_t, 5>> range::memo;
map<bdd_and_eq::key, unordered_map<spbdd, spbdd>> bdd_and_eq::memos;
map<range::key, builtins<leq_const>> range::bsyms, range::bnums, range::bchars;
//map<query::key, unordered_map<size_t, size_t>*> query::memos;
