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
#include <vector>
#include <cstdint>
#include <string>
#include <cstring>
#include <iostream>
#include <random>
#include <sstream>
#include <climits>
#include <stdexcept>
#include <cassert>
using namespace std;
//#define MEMO
#define er(x)	perror(x), exit(0)
#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define dot_after_q "expected '.' after query.\n"
#define if_expected "'if' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
#define RED     "\x1b[31m"
#define GREEN   "\x1b[32m"
#define YELLOW  "\x1b[33m"
#define BLUE    "\x1b[34m"
#define MAGENTA "\x1b[35m"
#define CYAN    "\x1b[36m"
#define COLOR_RESET   "\x1b[0m"
#ifdef MEMO
#define apply_ret(r, m) return m.emplace(t, res = (r)), res
#else
#define apply_ret(r, m) return r
#endif

typedef int64_t int_t;
typedef array<size_t, 3> node; //bdd node is a triple: varid,1-node-id,0-node-id
typedef const wchar_t* wstr;
typedef vector<int_t> term;
typedef vector<term> matrix;// set of relational terms
typedef vector<bool> bools;
typedef vector<bools> vbools;
template<> struct std::hash<node> {
	size_t operator()(const node& n) const { return n[0] + n[1] + n[2]; }
};
struct dictcmp {
	bool operator()(const pair<wstr, size_t>& x,
			const pair<wstr, size_t>& y) const {
		return	x.second != y.second ? x.second < y.second :
			wcsncmp(x.first, y.first, x.second) < 0;
	}
};

vector<node> &V = *new vector<node>; // all bdd nodes
unordered_map<node, size_t> M; // node to its index
map<pair<wstr, size_t>, int_t, dictcmp> syms_dict, vars_dict;
vector<wstr> syms;
vector<size_t> lens;
const int_t pad = 0;
const size_t F = 0, T = 1;

#ifdef MEMO
typedef array<size_t, 2> memo;
typedef array<size_t, 3> adtmemo;
typedef pair<const bool*, size_t> exmemo;
typedef pair<const bool*, memo> apexmemo;
typedef pair<const size_t*, size_t> permemo;
template<> struct std::hash<memo> { size_t operator()(const memo& m) const; };
template<> struct std::hash<exmemo> { size_t operator()(const exmemo&m)const;};
template<>struct std::hash<apexmemo>{size_t operator()(const apexmemo&m)const;};
template<> struct std::hash<permemo>{ size_t operator()(const permemo&m)const;};
unordered_map<memo, size_t> memo_and, memo_and_not, memo_or, memo_dt;
unordered_map<adtmemo, size_t> memo_adt;
unordered_map<exmemo, size_t> memo_ex;
unordered_map<apexmemo, size_t> memo_and_ex, memo_and_not_ex;
unordered_map<permemo, size_t> memo_permute;
#endif

size_t bdd_add_nocheck(const node& n) {
	size_t r;
	return M.emplace(n, r = V.size()), V.emplace_back(n), r;
}

void bdd_init() { bdd_add_nocheck({{0, 0, 0}}), bdd_add_nocheck({{0, 1, 1}}); }

size_t bdd_add(const node& n) {//create new bdd node,standard implementation
	if (n[1] == n[2]) return n[1];
	auto it = M.find(n);
	return it == M.end() ? bdd_add_nocheck(n) : it->second;
}

const node& getnode(size_t n)	{ return V[n]; }
bool leaf(size_t x)		{ return x == T || x == F; }
bool leaf(const node& x)	{ return !x[0]; }
bool trueleaf(const node& x)	{ return leaf(x) && x[1]; }
bool trueleaf(const size_t& x)	{ return x == T; }
size_t from_bit(size_t x ,bool v) {
	return bdd_add(v ? node{{x+1,T,F}} : node{{x+1,F,T}}); }
void dict_init() { syms.push_back(0), lens.push_back(0), syms_dict[{0, 0}]=pad;}
pair<wstr, size_t> dict_get(int_t t) { return { syms[t],lens[t] }; }
size_t nsyms() { return syms.size(); }

matrix from_bits(size_t x, size_t bits, size_t ar);
wostream& out(wostream& os, const node& n) { //print using ?: syntax
	return	leaf(n) ? os << (trueleaf(n) ? L'T' : L'F') :
		(out(os<<n[0]<<L'?',getnode(n[1])),out(os<<L':',getnode(n[2])));
}
wostream& out(wostream& os,size_t n){return out(os<<L'['<<n<<L']',getnode(n));}
wostream& operator<<(wostream& os, const pair<wstr, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) { os << p.first[n]; } return os;}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x){ os << (y?1:0); } return os; }
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) { os << y << endl; } return os; }
wostream& out(wostream& os, size_t db, size_t bits, size_t ar) {
	set<wstring> s;
	for (auto v : from_bits(db, bits, ar)) {
		wstringstream ss;
		for (auto k : v)
			if (!k) ss << L"* ";
			else if((size_t)k<(size_t)nsyms())ss<<dict_get(k)<<L' ';
			else ss << L'[' << k << L"] ";
		s.emplace(ss.str());
	}
	for (auto& x : s) os << x << endl;
	return os;
}

void memos_clear() {
#ifdef MEMO		
	memo_and.clear(), memo_and_not.clear(), memo_or.clear(),
	memo_permute.clear(), memo_and_ex.clear(), memo_and_not_ex.clear();
#endif		
}

int_t dict_get(wstr s, size_t len) {
	if (*s == L'?') {
		auto it = vars_dict.find({s, len});
		if (it != vars_dict.end()) return it->second;
		int_t r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	auto it = syms_dict.find({s, len});
	if (it != syms_dict.end()) return it->second;
	return	syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] =
		syms.size() - 1;
}

#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))
size_t dict_bits() { return msb(nsyms()-1); }
////////////////////////////////////////////////////////////////////////////////
struct rule { // a P-DATALOG rule in bdd form
	struct body {
		size_t sel = T, *perm = 0;
		bool *ex = 0;
//		~body() { if (perm) delete[] perm; if (ex) delete[] ex; }
	};
	bool neg = false;
	size_t hsym = T, npos = 0, nneg = 0, *sels = 0;
	vector<body> bd;

	rule() {}
	rule(matrix v, size_t bits);
	size_t step(size_t db, size_t bits, size_t ar) const;
//	~rule() { if (sels) delete sels; }
};

class lp { // [pfp] logic program
	int_t str_read(wstr *s); // parse a string and returns its dict id
	term term_read(wstr *s); // read raw term (no bdd)
	matrix rule_read(wstr *s); // read raw rule (no bdd)
public:
	vector<rule*> rules;
	size_t bits, ar, maxw;
	size_t db; // db's bdd root
	void prog_read(wstr s);
	void step(); // single pfp step
	bool pfp();
	void printdb(wostream& os);
};
////////////////////////////////////////////////////////////////////////////////
void sat(size_t v, size_t nvars, node n, bools& p, vbools& r) {
	if (leaf(n) && !trueleaf(n)) return;
	if (v < n[0])
		p[v-1] = true,  sat(v + 1, nvars, n, p, r),
		p[v-1] = false, sat(v + 1, nvars, n, p, r);
	else if (v != nvars+1)
		p[v-1] = true,  sat(v + 1, nvars, getnode(n[1]), p, r),
		p[v-1] = false, sat(v + 1, nvars, getnode(n[2]), p, r);
	else	r.push_back(p);
}

vbools allsat(size_t x, size_t nvars) {
	bools p(nvars);
	vbools r;
	return sat(1, nvars, getnode(x), p, r), r;
}

size_t bdd_or(size_t x, size_t y) {
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_or.find(t);
	if (it != memo_or.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (leaf(Vx)) apply_ret(trueleaf(Vx) ? T : y, memo_or);
       	const node &Vy = getnode(y);
	if (leaf(Vy)) apply_ret(trueleaf(Vy) ? T : x, memo_or);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret(a||b ? T : F, memo_or);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_add({{v, bdd_or(a, b), bdd_or(c, d)}}), memo_or);
}

size_t bdd_ex(size_t x, const bool* b) {
	node n = getnode(x);
	if (leaf(n)) return x;
#ifdef MEMO
	exmemo t = {b, x};
	auto it = memo_ex.find(t);
	if (it != memo_ex.end()) return it->second;
	size_t res;
#endif	
	if (b[n[0]-1]) {
		if (leaf(x = bdd_or(n[1], n[2]))) apply_ret(x, memo_ex);
		n = getnode(x);
	}
	apply_ret(bdd_add({{n[0], bdd_ex(n[1], b), bdd_ex(n[2], b)}}), memo_ex);
}

size_t bdd_and(size_t x, size_t y) {
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_and.find(t);
	if (it != memo_and.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (leaf(Vx)) apply_ret(trueleaf(Vx)?y:F, memo_and);
       	const node &Vy = getnode(y);
	if (leaf(Vy)) apply_ret(!trueleaf(Vy) ? F : x, memo_and);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret((a&&b)?T:F, memo_and);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_add({{v, bdd_and(a, b), bdd_and(c, d)}}), memo_and);
}

size_t bdd_deltail(size_t x, size_t h) {
	if (leaf(x)) return x;
#ifdef MEMO
	memo t = {{x, h}};
	auto it = memo_dt.find(t);
	if (it != memo_dt.end()) return it->second;
	size_t res;
#endif	
	node n = getnode(x);
	if (n[0] <= h)
		apply_ret(bdd_add({{n[0], bdd_deltail(n[1],h),
			bdd_deltail(n[2],h)}}), memo_dt);
	apply_ret(n[1] == F && n[2] == F ? F : T, memo_dt);
}    

size_t bdd_and_deltail(size_t x, size_t y, size_t h) {
#ifdef MEMO
	adtmemo t = {{x, y, h}};
	auto it = memo_adt.find(t);
	if (it != memo_adt.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (leaf(Vx)) apply_ret(trueleaf(Vx)? bdd_deltail(y, h) : F, memo_adt);
       	const node &Vy = getnode(y);
	if (leaf(Vy)) apply_ret(!trueleaf(Vy) ? F : bdd_deltail(x, h),memo_adt);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret((a&&b)?T:F, memo_adt);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_deltail(bdd_add({{v, bdd_and_deltail(a, b, h),
		bdd_and_deltail(c, d, h)}}), h), memo_adt);
}

size_t bdd_and_ex(size_t x, size_t y, const bool* s) {
#ifdef MEMO
	apexmemo t = {s, {{x, y}}};
	auto it = memo_and_ex.find(t);
	if (it != memo_and_ex.end()) return it->second;
#endif	
	size_t res;
	const node &Vx = getnode(x), &Vy = getnode(y);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if (leaf(Vx)) {
		res = trueleaf(Vx) ? bdd_ex(y, s) : F;
		goto ret;
	}
	if (leaf(Vy)) {
		res = trueleaf(Vy) ? bdd_ex(x, s) : F;
		goto ret;
	}
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) { res = (a&&b)?T:F; goto ret; }
	else if ((v = vx) < vy || !vy) b = d = y;
	if (s[v-1]) res = bdd_or(bdd_and_ex(a, b, s), bdd_and_ex(c, d, s));
	else res = bdd_add({{v, bdd_and_ex(a, b, s), bdd_and_ex(c, d, s)}});
ret:	apply_ret(res, memo_and_ex);
}

size_t bdd_and_not(size_t x, size_t y) {
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_and_not.find(t);
	if (it != memo_and_not.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (leaf(Vx) && !trueleaf(Vx)) apply_ret(F, memo_and_not);
       	const node &Vy = getnode(y);
	if (leaf(Vy)) apply_ret(trueleaf(Vy) ? F : x, memo_and_not);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret((a&&!b)?T:F, memo_and_not);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_add({{v,bdd_and_not(a,b),bdd_and_not(c,d)}}),memo_and_not);
}

size_t bdd_and_not_ex(size_t x, size_t y, const bool* s) {
#ifdef MEMO
	apexmemo t = {s, {{x, y}}};
	auto it = memo_and_not_ex.find(t);
	if (it != memo_and_not_ex.end()) return it->second;
#endif	
	size_t res;
	const node &Vx = getnode(x), &Vy = getnode(y);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if (leaf(Vx) && !trueleaf(Vx)) {
		res = F;
		goto ret;
	}
	if (leaf(Vy)) {
		res = trueleaf(Vy) ? F : bdd_ex(x, s);
		goto ret;
	}
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) { res = (a && !b)?T:F; goto ret; }
	else if ((v = vx) < vy || !vy) b = d = y;
	if (s[v-1]) res = bdd_or(bdd_and_not_ex(a,b,s), bdd_and_not_ex(c,d,s));
	else res = bdd_add({{v, bdd_and_not_ex(a,b,s), bdd_and_not_ex(c,d,s)}});
ret:	apply_ret(res, memo_and_not_ex);
}

size_t ite(size_t v, size_t t, size_t e) {
	const node &x = getnode(t), &y = getnode(e);
	if ((leaf(x)||v<x[0]) && (leaf(y)||v<y[0])) return bdd_add({{v+1,t,e}});
	return bdd_or(bdd_and(from_bit(v,true),t),bdd_and(from_bit(v,false),e));
}

size_t bdd_permute(size_t x, const size_t* m) {//overlapping rename
#ifdef MEMO
	permemo t = {m, x};
	auto it = memo_permute.find(t);
	if (it != memo_permute.end()) return it->second;
	size_t res;
#endif	
	const node n = getnode(x);
	if (leaf(n)) apply_ret(x, memo_permute);
	size_t v = m[n[0]-1];
	apply_ret(ite(v, bdd_permute(n[1], m), bdd_permute(n[2], m)), memo_permute);
}

size_t from_eq(size_t x, size_t y) {
	return bdd_or(	bdd_and(from_bit(x, true), from_bit(y, true)),
			bdd_and(from_bit(x, false),from_bit(y, false)));
}

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
matrix from_bits(size_t x, size_t bits, size_t ar) {
	vbools s = allsat(x, bits * ar);
	matrix r(s.size());
	for (term& v : r) v = term(ar, 0);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i)
			for (b = 0; b != bits; ++b)
				if (s[n][i * bits + b])
					r[n][i] |= 1 << (bits - b - 1);
	return r;
}
////////////////////////////////////////////////////////////////////////////////
int_t lp::str_read(wstr *s) {
	wstr t;
	while (**s && iswspace(**s)) ++*s;
	if (!**s) throw runtime_error("identifier expected");
	if (*(t = *s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == *s) throw runtime_error("identifier expected");
	int_t r = dict_get(*s, t - *s);
	while (*t && iswspace(*t)) ++t;
	return *s = t, r;
}

term lp::term_read(wstr *s) {
	term r;
	while (iswspace(**s)) ++*s;
	if (!**s) return r;
	bool b = **s == L'~';
	if (b) ++*s, r.push_back(-1); else r.push_back(1);
	do {
		while (iswspace(**s)) ++*s;
		if (**s == L',') return ++*s, r;
		if (**s == L'.' || **s == L':') return r;
		r.push_back(str_read(s));
	} while (**s);
	er("term_read(): unexpected parsing error");
}

matrix lp::rule_read(wstr *s) {
	term t;
	matrix r;
	if ((t = term_read(s)).empty()) return r;
	r.push_back(t);
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	if (*((*s)++) != L':' || *((*s)++) != L'-') er(sep_expected);
loop:	if ((t = term_read(s)).empty()) er("term expected");
	r.push_back(t);
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	if (**s == L':') er("',' expected");
	goto loop;
}

void lp::prog_read(wstr s) {
	vector<matrix> r;
	db = F;
	size_t l;
	ar = maxw = 0;
	for (matrix t; !(t = rule_read(&s)).empty(); r.push_back(t)) {
		for (const term& x : t) // we support a single rel arity
			ar = max(ar, x.size()-1); // so we'll pad everything
		maxw = max(maxw, t.size() - 1);
	}
	for (matrix& x : r)
		for (term& y : x)
			if ((l=y.size()) < ar+1)
				y.resize(ar+1),
				fill(y.begin() + l, y.end(), pad);//the padding
	bits = dict_bits();
	for (const matrix& x : r)
	 	if (x.size() == 1) db = bdd_or(db, rule(x, bits).hsym);//fact
		else rules.emplace_back(new rule(x, bits));
}

rule::rule(matrix v, size_t bits) {
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
			if (v[i][j] >= 0)
				d.sel = bdd_and(d.sel,
					from_int(v[i][j], bits, j * bits));
			else if ((it = m.find(v[i][j])) != m.end())
				for (b = 0; b != bits; ++b)
					d.ex[b+j*bits] = true,
					d.sel = bdd_and(d.sel, from_eq(b+j*bits,
						b+it->second*bits));
			else 	m.emplace(v[i][j], j), d.sel = bdd_and(d.sel,
					from_range(nsyms(), bits, j * bits));
		//out(wcout<<"d.sel"<<endl, d.sel, bits, ar)<<endl;
		m.clear(), bd.push_back(d);
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
	sels = new size_t[v.size() - 1];
}

size_t rule::step(size_t db, size_t bits, size_t ar) const {
	size_t n = 0, vars = T;
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
	for (n = 0; n != bd.size(); ++n)
		if (F == (vars=bdd_and(vars, bdd_permute(sels[n], bd[n].perm))))
			return F;
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
			return printdb(wcout), d == db;
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
void lp::printdb(wostream& os) { out(os, db, bits, ar); }
////////////////////////////////////////////////////////////////////////////////
int main() {
	setlocale(LC_ALL, ""), bdd_init(), dict_init();
//	test_range();
	lp p;
	wstring s = file_read_text(stdin); // got to stay in memory
	p.prog_read(s.c_str());
	if (!p.pfp()) wcout << "unsat" << endl;
	return 0;
}
