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
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <cstring>
#include <iostream>
#include <random>
#include <sstream>
#include <climits>
#include <stdexcept>
#include <cassert>
#include "tml.h"
using namespace std;

void tml_init() { bdd_init(); }

matrix from_bits(size_t x, size_t bits, size_t ar);
wostream& out(wostream& os, const node& n) { //print using ?: syntax
	return	leaf(n) ? os << (trueleaf(n) ? L'T' : L'F') :
		(out(os<<n[0]<<L'?',getnode(n[1])),out(os<<L':',getnode(n[2])));
}
wostream& out(wostream& os,size_t n){return out(os<<L'['<<n<<L']',getnode(n));}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x){ os << (y?1:0); } return os; }
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) { os << y << endl; } return os; }

struct rule { // a P-DATALOG rule in bdd form
	struct body {
		size_t sel = T, *perm = 0;
		bool *ex = 0;
		body() {}
		body(body&&b):sel(b.sel),perm(b.perm),ex(b.ex){b.perm=0,b.ex=0;}
		~body() { if (perm) delete[] perm; if (ex) delete[] ex; }
	};
	bool neg = false;
	size_t hsym = T, npos = 0, nneg = 0, *sels = 0;
	vector<body> bd;

	rule() {}
	rule(rule&& r) : neg(r.neg), hsym(r.hsym), npos(r.npos), nneg(r.nneg),
		sels(r.sels) { r.sels = 0; }
	rule(matrix v, size_t bits, size_t dsz);
	size_t step(size_t db, size_t bits, size_t ar) const;
	~rule() { if (sels) delete sels; }
};
////////////////////////////////////////////////////////////////////////////////
size_t from_int(size_t x, size_t bits, size_t offset) {
	size_t r = T, b = bits--;
	while (b--) r = bdd_and(r, from_bit(bits - b + offset, x&(1<<b)));
	return r;
}
/*
size_t from_leq(size_t max, size_t bits, size_t offset) {
	size_t r = T, t = msb(max);
	for (size_t b = 0; b != bits; ++b) {
		if (max&(1<<(bits-b-1))) r = ite(b + offset, r, T);
		else r = ite(b + offset, F, r);
//		wcout << allsat(r, bits) << endl << 't'<<endl;
	}
	return r;
}
*/
size_t from_range(size_t max, size_t bits, size_t offset) {
	size_t x = F;
	for (size_t n = 1; n < max; ++n) x = bdd_or(x,from_int(n,bits,offset));
	return x;
/*	, n = 0;
	size_t t = msb(max);
	for (n = 0; n != bits; ++n) x = bdd_or(x, from_bit(offset + n, 1));
	wcout << allsat(x, bits) << endl;
	for (n = 0; n != bits-msb(max); ++n) x = bdd_and(x, from_bit(offset + n, 0));
	wcout << allsat(x, bits) << endl;
	size_t l = from_leq(max, bits, offset);
	wcout << allsat(l, bits) << endl;
	return bdd_and(l, x);*/
}
/*
void test_range() {
	size_t x = 9, y = 5, z = 11, o = 0; // 1101 = 13, 1011 = 11
	size_t m = from_range(y, 5, o);
//	wcout << allsat(from_range(1, 3, 0), 3) << endl;
//	wcout << allsat(from_int(y, 6, o), 6) << endl << y << endl;
//	wcout << allsat(from_int(x, 6, o), 6) << endl << x << endl;
	wcout << allsat(m, 5);
//	assert(y<<o == bdd_and(from_int(y, 6, o), m));
//	assert(F == bdd_and(from_int(z, 6, o), m));
	exit(0);
}
*/
////////////////////////////////////////////////////////////////////////////////
void lp::rule_add(const matrix& t) {
	rawrules.push_front(t);
	for (const term& x : t) // we support a single rel arity
		ar = max(ar, x.size()-1); // so we'll pad everything
	maxw = max(maxw, t.size() - 1);
}

void lp::compile(size_t _bits, size_t dsz) {
	size_t l;
	bits = _bits;
	for (matrix& x : rawrules)
		for (term& y : x)
			if ((l=y.size()) < ar+1)
				y.resize(ar+1),
				fill(y.begin() + l, y.end(), pad);//the padding
	for (const matrix& x : rawrules)
	 	if (x.size() == 1) db = bdd_or(db, rule(x,bits,dsz).hsym);//fact
		else rules.emplace_back(new rule(x, bits, dsz));
	rawrules.clear();
}

vbools lp::allsat(size_t x) { return ::allsat(x, bits * ar); }

rule::rule(matrix v, size_t bits, size_t dsz) {
	matrix t; // put negs after poss and count them
	t.push_back(v[0]);
	size_t i, j, b, ar = v[0].size() - 1, k = ar, nvars;
	for (i=1; i!=v.size(); ++i) if (v[i][0]>0) ++npos, t.push_back(v[i]);
	for (i=1; i!=v.size(); ++i) if (v[i][0]<0) ++nneg, t.push_back(v[i]);
	v = move(t);
	neg = v[0][0] < 0;
	set<int_t> vars;
	for (term& x : v) {
		x.erase(x.begin());
		for (int_t& y : x) if (y < 0) vars.emplace(y);
	}
	nvars = vars.size();
	map<int_t, size_t> m;
	auto it = m.end();
	for (i = 1; i != v.size(); ++i) { // init, sel, ex and local eq
		body d;
		d.ex = (bool*)memset(new bool[bits*ar],0,sizeof(bool)*bits*ar),
		d.perm = new size_t[(ar + nvars) * bits];
		for (b = 0; b != (ar + nvars) * bits; ++b) d.perm[b] = b;
		for (j = 0; j != ar; ++j)
			if (v[i][j] >= 0) {
				d.sel = bdd_and(d.sel,
					from_int(v[i][j], bits, j * bits));
				for (b = 0; b != bits; ++b) d.ex[b+j*bits]=true;
			} else if ((it = m.find(v[i][j])) != m.end())
				for (b = 0; b != bits; ++b)
					d.ex[b+j*bits] = true,
					d.sel = bdd_and(d.sel, from_eq(b+j*bits,
						b+it->second*bits));
			else 	m.emplace(v[i][j], j), d.sel = bdd_and(d.sel,
					from_range(dsz, bits, j * bits));
		//out(wcout<<"d.sel"<<endl, d.sel, bits, ar)<<endl;
		m.clear(), bd.push_back(move(d));
	}
	for (j = 0; j != ar; ++j) // hsym
		if (v[0][j] >= 0)
			hsym = bdd_and(hsym, from_int(v[0][j], bits, j * bits));
		else if (m.end() == (it=m.find(v[0][j]))) m.emplace(v[0][j], j);
		else for (b = 0; b != bits; ++b)
			hsym=bdd_and(hsym,from_eq(b+j*bits, b+it->second*bits));
	//out(wcout<<"hsym"<<endl, hsym, bits, ar)<<endl;
	for (i = 0; i != v.size() - 1; ++i) // var permutations
		for (j = 0; j != ar; ++j)
			if (v[i+1][j] < 0) {
				if ((it = m.find(v[i+1][j])) == m.end())
					it = m.emplace(v[i+1][j], k++).first;
				for (b = 0; b != bits; ++b)
					bd[i].perm[b+j*bits]=b+it->second*bits;
			}
	if (v.size() > 1) sels = new size_t[v.size() - 1];
}

size_t rule::step(size_t db, size_t bits, size_t ar) const {
	size_t n = 0, vars = T, p;
//	out(wcout<<"db:"<<endl, db, bits, ar);
	for (; n != npos; ++n)
		if (F == (sels[n] = bdd_and_ex(bd[n].sel, db, bd[n].ex)))
			return F;
//		else {
//			out(wcout<<"db.sel"<<n<<endl, bd[n].sel, bits, ar)<<endl;
//			out(wcout<<"sel"<<n<<endl, sels[n], bits, ar)<<endl;
//		}
	for (; n != nneg+npos; ++n)
		if (F == (sels[n] = bdd_and_not_ex(bd[n].sel, db, bd[n].ex)))
			return F;
//		else {
//			out(wcout<<"db.sel"<<n<<endl, bd[n].sel, bits, ar)<<endl;
//			out(wcout<<"sel"<<n<<endl, sels[n], bits, ar)<<endl;
//		}
	for (n = 0; n != bd.size(); ++n) {
		p = bdd_permute(sels[n], bd[n].perm);
//		out(wcout<<"p"<<n<<endl, p, bits, ar)<<endl;
//		out(wcout<<"vars"<<n<<endl, p, bits, ar)<<endl;
		if (F == (vars=bdd_and(vars, p)))
			return F;
//		out(wcout<<"vars"<<n<<endl, vars, bits, ar)<<endl;
	}
	return bdd_and_deltail(hsym, vars, bits * ar);
}

void lp::step() {
	size_t add = F, del = F, s;
	for (const rule* r : rules) {
		(r->neg?del:add) = bdd_or(r->step(db, bits, ar),r->neg?del:add);
//		memos_clear();
	}
	if ((s = bdd_and_not(add, del)) == F && add != F)
		db = F; // detect contradiction
	else db = bdd_or(bdd_and_not(db, del), s);
}

bool lp::pfp() {
	size_t d;
	for (set<int_t> s;;)
		if (s.emplace(d = db), step(), s.find(db) != s.end())
			return d == db;
}
////////////////////////////////////////////////////////////////////////////////
wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n != 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = 0; break; }
		else if (c == L'#') skip = 1;
		else if (c == L'\r' || c == L'\n') skip = 0, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0, ss << buf;
		goto next;
	} else if (skip) goto next;
	return ss.str();
}
#ifdef MEMO
size_t std::hash<memo>::operator()(const memo& m) const { return m[0] + m[1]; }
size_t std::hash<apexmemo>::operator()(const apexmemo& m) const {
	static std::hash<memo> h;
	return (size_t)m.first + h(m.second);
}
size_t std::hash<permemo>::operator()(const permemo& m) const {
	return (size_t)m.first + (size_t)m.second;
}
size_t std::hash<exmemo>::operator()(const exmemo& m) const {
	return (size_t)m.first + (size_t)m.second;
}
#endif
