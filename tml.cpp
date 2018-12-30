// LICENSE
// This software is free for use and redistribution while including this license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission.  This license may be modified over time by the Author.
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

typedef int64_t int_t;
typedef array<size_t, 3> node; // bdd node is a triple: varid, 1-node-id, 0-node-id
typedef const wchar_t* wstr;
template<typename K> using matrix = vector<vector<K>>; // used as a set of terms (e.g. rule)
typedef vector<bool> bools;
typedef vector<bools> vbools;
class bdds;
typedef tuple<const bdds*, size_t, size_t> memo;
typedef tuple<const bdds*, const bool*, size_t, size_t> exmemo;
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
////////////////////////////////////////////////////////////////////////////////////////////////////
template<> struct std::hash<node> {
	size_t operator()(const node& n) const { return n[0] + n[1] + n[2]; }
};
template<> struct std::hash<memo> { size_t operator()(const memo& m) const; };
template<> struct std::hash<exmemo> { size_t operator()(const exmemo& m) const; };
template<> struct std::hash<pair<const bdds*, size_t>> {
	size_t operator()(const pair<const bdds*, size_t>& m) const;
};
template<> struct std::hash<pair<size_t, const size_t*>> {
	size_t operator()(const pair<size_t, const size_t*>& m) const { return m.first + (size_t)m.second; }
};
////////////////////////////////////////////////////////////////////////////////////////////////////
struct rule { // a [P-DATALOG] rule in bdd form with additional information
	bool neg;
	size_t h, hsym; // bdd root and head syms
	size_t w; // nbodies, will determine the virtual power
	bool *x; // existentials
	size_t *hvars; // how to permute body vars to head vars
};
////////////////////////////////////////////////////////////////////////////////////////////////////
class bdds_base {
	vector<node> V; // all nodes
	unordered_map<node, size_t> M; // node to its index
protected:
	size_t dim = 1; // used for implicit power
	const size_t nvars;
	size_t add_nocheck(const node& n) {
		size_t r;
		return M.emplace(n, r = V.size()), V.emplace_back(n), r;
	}
	bdds_base(size_t nvars) : nvars(nvars) { add_nocheck({{0, 0, 0}}), add_nocheck({{0, 1, 1}}); }
public:
	size_t root = 0, maxbdd; // used for implicit power
	static const size_t F, T;
	size_t setpow(size_t _root, size_t _dim, size_t maxw) {
		root = _root, dim = _dim, maxbdd = (size_t)1 << ((sizeof(int_t)<<3)/maxw);
		return root;
	}
	size_t add(const node& n) { // create new bdd node, standard implementation
		if (n[1] == n[2]) return n[1];
		if (auto it = M.find(n); it != M.end()) return it->second;
		return add_nocheck(n);
	}
	node getnode(size_t n) const { // returns a bdd node considering virtual powers
		if (dim == 1) return V[n];
		const size_t m = n % maxbdd, d = n / maxbdd;
		node r = V[m];
		if (r[0]) r[0] += nvars * d;
		if (trueleaf(r[1])) { if (d<dim-1) r[1] = root + maxbdd * (d+1); }
		else if (!leaf(r[1])) r[1] += maxbdd * d;
		if (trueleaf(r[2])) { if (d<dim-1) r[2] = root + maxbdd * (d+1); }
		else if (!leaf(r[2])) r[2] += maxbdd * d;
		return r;
	}
	static bool leaf(size_t x) { return x == T || x == F; }
	static bool leaf(const node& x) { return !x[0]; }
	static bool trueleaf(const node& x) { return leaf(x) && x[1]; }
	static bool trueleaf(const size_t& x) { return x == T; }
	wostream& out(wostream& os, const node& n) const; // print a bdd using ?: syntax
	wostream& out(wostream& os, size_t n) const	{ return out(os<< L'['<<n<<L']' , getnode(n)); }
	size_t size() const { return V.size(); }
};
const size_t bdds_base::F = 0;
const size_t bdds_base::T = 1;
////////////////////////////////////////////////////////////////////////////////////////////////////
vbools& operator*=(vbools& x, const pair<const vbools&, size_t>& y); // to be used with allsat()

class bdds : public bdds_base { // holding functions only, therefore tbd: dont use it as an object
	void sat(size_t v, size_t nvars, node n, bools& p, vbools& r) const;
	unordered_map<memo, size_t> memo_and, memo_and_not, memo_or;
	unordered_map<exmemo, size_t> memo_and_ex;
	unordered_map<pair<const bdds*, size_t>, size_t> memo_copy;
	unordered_map<pair<size_t, const size_t*>, size_t> memo_permute;
public:
	bdds(size_t nvars) : bdds_base(nvars) {}
	size_t from_bit(size_t x, bool v) { return add(v ? node{{x+1, T, F}} : node{{x+1, F, T}}); }
	size_t ite(size_t v, size_t t, size_t e);
	size_t copy(const bdds& b, size_t x);
	static size_t apply_and(bdds& src, size_t x, bdds& dst, size_t y);
	static size_t apply_and_not(bdds& src, size_t x, bdds& dst, size_t y);
	static size_t apply_or(bdds& src, size_t x, bdds& dst, size_t y);
	static size_t apply_and_ex_perm(bdds& src, size_t x, bdds& dst, size_t y, const bool* s, const size_t* p, size_t sz);
	template<typename op_t> static size_t apply(bdds& b, size_t x, bdds& r, const op_t& op);//unary
	template<typename op_t> static size_t apply(const bdds& b, size_t x,bdds& r, const op_t& op);//unary
	size_t permute(size_t x, const size_t*, size_t sz);
	// helper constructors
	size_t from_eq(size_t x, size_t y); // a bdd saying "x=y"
	template<typename K> rule from_rule(matrix<K> v, const size_t bits, const size_t ar);
	template<typename K>
	void from_arg(	size_t i, size_t j, size_t &k, K vij, size_t bits, size_t ar,
			const map<K, int_t>&, map<K, array<size_t, 2>>&, rule &r, size_t &npad);
	template<typename K> matrix<K> from_bits(size_t x, size_t bits, size_t ar);
	// helper apply() variations
	size_t bdd_or(size_t x, size_t y)	{ return apply_or(*this, x, *this, y); } 
	size_t bdd_and(size_t x, size_t y)	{ return apply_and(*this, x, *this, y); } 
	size_t bdd_and_not(size_t x, size_t y){ return apply_and_not(*this, x, *this, y); }
	vbools allsat(size_t x, size_t nvars) const;
	void memos_clear() { /*memo_and.clear(), memo_and_not.clear(), memo_or.clear(), memo_copy.clear(), memo_permute.clear(),*/ memo_and_ex.clear(); }
	using bdds_base::add;
	using bdds_base::out;
};

struct op_exists { // existential quantification, to be used with apply()
	const bool* s;
	size_t sz;
	op_exists(const bool* s, size_t sz) : s(s), sz(sz) { }
	node operator()(bdds& b, const node& n) const {
		return n[0] && n[0] <= sz && s[n[0]-1] ? b.getnode(b.bdd_or(n[1], n[2])) : n;
	}
};
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K> class dict_t { // handles representation of strings as unique integers
	struct dictcmp {
		bool operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const;
	};
	map<pair<wstr, size_t>, K, dictcmp> syms_dict, vars_dict;
	vector<wstr> syms;
	vector<size_t> lens;
public:
	const K pad = 0;
	dict_t() { syms.push_back(0), lens.push_back(0), syms_dict[{0, 0}] = pad; }
	K operator()(wstr s, size_t len);
	pair<wstr, size_t> operator()(K t) const { return { syms[t], lens[t] }; }
	size_t bits() const { return (sizeof(K)<<3) - __builtin_clz(syms.size()); }
	size_t nsyms() const { return syms.size(); }
};
wostream& operator<<(wostream& os, const pair<wstr, size_t>& p) {
	for (size_t n = 0; n < p.second; ++n) os << p.first[n];
	return os;
}
template<typename K>
wostream& out(wostream& os, bdds& b, size_t db, size_t bits, size_t ar, const class dict_t<K>& d);
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K> class lp { // [pfp] logic program
	dict_t<K> dict; // hold its own dict so we can determine the universe size
	bdds *pprog, *pdbs; // separate bdds for prog and db cause db is a virtual power
	vector<rule> rules; // prog's rules

	K str_read(wstr *s); // parser's helper, reads a string and returns its dict id
	vector<K> term_read(wstr *s); // read raw term (no bdd)
	matrix<K> rule_read(wstr *s); // read raw rule (no bdd)
	size_t bits, ar, maxw;
public:
	size_t db; // db's bdd root
	void prog_read(wstr s);
	void step(); // single pfp step
	bool pfp();
	void printdb(wostream& os) { out<K>(os, *pdbs, db, bits, ar, dict); }
};
////////////////////////////////////////////////////////////////////////////////////////////////////
wostream& operator<<(wostream& os, const bools& x) { for (auto y:x) os << (y?'1':'0');return os; }
wostream& operator<<(wostream& os, const vbools& x) { for (auto y:x) os << y << endl; return os; }
template<typename K> wostream& out(wostream& os, bdds& b, size_t db, size_t bits, size_t ar, const dict_t<K>& d) {
	for (auto v : b.from_bits<K>(db, bits, ar)) {
		for (auto k : v)
			if (!k) os << L"* ";
			else if ((size_t)k < (size_t)d.nsyms()) os << d(k) << L' ';
			else os << L'[' << k << L"] ";
		os << endl;
	}
	return os;
}

void bdds::sat(size_t v, size_t nvars, node n, bools& p, vbools& r) const {
	if (leaf(n) && !trueleaf(n)) return;
	//assert(v <= nvars+1);
	if (v<n[0]) p[v-1] = true, sat(v+1, nvars, n, p, r), p[v-1]=false, sat(v+1, nvars, n, p, r);
	else if (v == nvars+1) r.push_back(p);
	else p[v-1]=true, sat(v+1,nvars,getnode(n[1]),p,r), p[v-1]=false, sat(v+1,nvars,getnode(n[2]),p,r);
}

vbools bdds::allsat(size_t x, size_t nvars) const {
	bools p;
	p.resize(nvars);
	vbools r;
	return sat(1, nvars, getnode(x), p, r), r;
}

size_t bdds::from_eq(size_t x, size_t y) {
	return bdd_or(	bdd_and(from_bit(x, true), from_bit(y, true)),
			bdd_and(from_bit(x, false),from_bit(y, false)));
}

wostream& bdds_base::out(wostream& os, const node& n) const {
	if (leaf(n)) return os << (trueleaf(n) ? L'T' : L'F');
	else return out(os << n[0] << L'?', n[1]), out(os << L':', n[2]);
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename op_t> size_t bdds::apply(const bdds& b, size_t x, bdds& r, const op_t& op) { //unary
	node n = op(b, b.getnode(x));
	return r.add({n[0], leaf(n[1])?n[1]:apply(b,n[1],r,op), leaf(n[2])?n[2]:apply(b,n[2],r,op)});
}

template<typename op_t> size_t bdds::apply(bdds& b, size_t x, bdds& r, const op_t& op) { // nonconst
	node n = op(b, b.getnode(x));
	return r.add({{n[0], leaf(n[1])?n[1]:apply(b,n[1],r,op), leaf(n[2])?n[2]:apply(b,n[2],r,op)}});
}

size_t bdds::ite(size_t v, size_t t, size_t e) {
	node x = getnode(t), y = getnode(e);
	if ((leaf(x) || v < x[0]) && (leaf(y) || v < y[0])) return add({{v+1,t,e}});
	return bdd_or(bdd_and(from_bit(v, true), t), bdd_and(from_bit(v, false), e));
}

// [overlapping] rename
size_t bdds::permute(size_t x, const size_t* m, size_t sz) {
	auto t = make_pair(x, m);
	auto it = memo_permute.find(t);
	if (it != memo_permute.end()) return it->second;
	node n = getnode(x);
	size_t res = leaf(n) ? x : ite(n[0] <= sz ? m[n[0]-1] : (n[0]-1), permute(n[1],m,sz), permute(n[2],m,sz));
	return memo_permute.emplace(t, res), res;
}
size_t bdds::copy(const bdds& b, size_t x) {
	if (leaf(x)) return x;
	auto t = make_pair(&b, x);
	auto it = memo_copy.find(t);
	if (it != memo_copy.end()) return it->second;
	node n = b.getnode(x);
	size_t res = add({n[0], copy(b, n[1]), copy(b, n[2])});
	return memo_copy.emplace(t, res), res;
}
size_t bdds::apply_and(bdds& src, size_t x, bdds& dst, size_t y) {
	const auto t = make_tuple(&dst, x, y);
	auto it = src.memo_and.find(t);
	if (it != src.memo_and.end()) return it->second;
	size_t res;
	const node &Vx = src.getnode(x);
	if (leaf(Vx)) return src.memo_and.emplace(t, res = trueleaf(Vx) ? y : F), res;
       	const node &Vy = dst.getnode(y);
	if (leaf(Vy)) return src.memo_and.emplace(t, res = !trueleaf(Vy) ? F : &src == &dst ? x : dst.copy(src, x)), res;
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) return src.memo_and.emplace(t, res = (a&&b)?T:F), res;
	else if ((v = vx) < vy || !vy) b = d = y;
	return src.memo_and.emplace(t, res = dst.add({{v, apply_and(src, a, dst, b), apply_and(src, c, dst, d)}})), res;
}
size_t bdds::apply_and_ex_perm(bdds& src, size_t x, bdds& dst, size_t y, const bool* s, const size_t* p, size_t sz) {
	const auto t = make_tuple(&dst, s, x, y);
	auto it = src.memo_and_ex.find(t);
	if (it != src.memo_and_ex.end()) return it->second;
	size_t res;
	const node Vx = src.getnode(x);
       	const node Vy = dst.getnode(y);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if (leaf(Vx)) {
		res = trueleaf(Vx) ? apply(dst, y, dst, op_exists(s, sz)) : F;
		goto ret;
	}
	if (leaf(Vy)) {
		res = !trueleaf(Vy) ? F : &src == &dst ? apply(dst, x, dst, op_exists(s, sz)) : apply(dst, dst.copy(src, x), dst, op_exists(s, sz));
		goto ret;
	}
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) {
		res = (a&&b)?T:F;
		goto ret;
	}
	else if ((v = vx) < vy || !vy) b = d = y;
	if (v <= sz && s[v-1]) {
		res = dst.bdd_or(apply_and_ex_perm(src, a, dst, b, s, p, sz), apply_and_ex_perm(src, c, dst, d, s, p, sz));
		goto ret;
	}
	res = dst.add({{v, apply_and_ex_perm(src, a, dst, b, s, p, sz), apply_and_ex_perm(src, c, dst, d, s, p, sz)}});
ret:
	return src.memo_and_ex.emplace(t, res = dst.permute(res, p, sz)), res;
}
size_t bdds::apply_and_not(bdds& src, size_t x, bdds& dst, size_t y) {
	const auto t = make_tuple(&dst, x, y);
	auto it = src.memo_and_not.find(t);
	if (it != src.memo_and_not.end()) return it->second;
	size_t res;
	const node &Vx = src.getnode(x);
	if (leaf(Vx) && !trueleaf(Vx)) return src.memo_and_not.emplace(t, F), F;
       	const node &Vy = src.getnode(y);
	if (leaf(Vy)) return src.memo_and_not.emplace(t, res = trueleaf(Vy) ? F : &src == &dst ? x : dst.copy(src, x)), res;
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) return src.memo_and_not.emplace(t, res = (a&&!b)?T:F), res;
	else if ((v = vx) < vy || !vy) b = d = y;
	return src.memo_and_not.emplace(t, res = dst.add({{v, apply_and_not(src, a, dst, b), apply_and_not(src, c, dst, d)}})), res;
}
size_t bdds::apply_or(bdds& src, size_t x, bdds& dst, size_t y) {
	const auto t = make_tuple(&dst, x, y);
	auto it = src.memo_or.find(t);
	if (it != src.memo_or.end()) return it->second;
	size_t res;
	const node &Vx = src.getnode(x);
	if (leaf(Vx)) return src.memo_or.emplace(t, res = trueleaf(Vx) ? T : y), res;
       	const node &Vy = dst.getnode(y);
	if (leaf(Vy)) return src.memo_or.emplace(t, res = trueleaf(Vy) ? T : &src == &dst ? x : dst.copy(src, x)), res;
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) return src.memo_or.emplace(t, res = (a||b)?T:F), res;
	else if ((v = vx) < vy || !vy) b = d = y;
	return src.memo_or.emplace(t, res = dst.add({{v, apply_or(src, a, dst, b), apply_or(src, c, dst, d)}})), res;
}
////////////////////////////////////////////////////////////////////////////////////////////////////
#define BIT(term,arg) ((term*bits+b)*ar+arg)
template<typename K> matrix<K> bdds::from_bits(size_t x, size_t bits, size_t ar) {
	vbools s = allsat(x, bits * ar * dim);
	matrix<K> r(s.size());
	for (vector<K>& v : r) v = vector<K>(dim * ar, 0);
	size_t n = 0, i, b;
	for (const bools& x : s) {
		for (i = 0; i != ar * dim; ++i)
			for (b = 0; b != bits; ++b)
				if (x[BIT(0, i)])
					r[n][i] |= 1 << b;
		++n;
	}
	return r;
}
template<typename K>
void bdds::from_arg(size_t i, size_t j, size_t &k, K vij, size_t bits, size_t ar,
	const map<K, int_t>& hvars, map<K, array<size_t, 2>>& m, rule &r, size_t &npad) {
	size_t notpad, b;
	if (auto it = m.find(vij); it != m.end()) { // if seen
		for (b=0; b!=bits; ++b)	k = bdd_and(k, from_eq(BIT(i,j), BIT(it->second[0], it->second[1])));
		if (hvars.find(vij) != hvars.end()) // existential out if headvar
			for (b=0; b!=bits; ++b) r.x[BIT(i,j)] = true;
	} else if (m.emplace(vij, array<size_t, 2>{ {i, j} }); vij >= 0) // sym
		for (b=0; b!=bits; ++b) k = bdd_and(k, from_bit(BIT(i,j), vij&(1<<b))), r.x[BIT(i,j)] = true;
	else {
		for (b=0, notpad = T; b!=bits; ++b) notpad = bdd_and(notpad, from_bit(BIT(i, j), false));
		npad = bdd_or(npad, notpad);
		if (auto jt = hvars.find(vij); jt == hvars.end()) //non-head var
			for (b=0; b!=bits; ++b) r.x[BIT(i,j)] = true;
		else for (b=0; b!=bits; ++b) if (BIT(i,j) != BIT(0, jt->second)) r.hvars[BIT(i,j)] = BIT(0, jt->second);
	}
}
template<typename K> rule bdds::from_rule(matrix<K> v, const size_t bits, const size_t ar) {
	size_t i, j, b, k, npad = F;
	map<K, int_t> hvars;
	vector<K>& head = v[v.size() - 1];
	bool bneg;
	rule r;
	r.h = r.hsym = T, r.neg = head[0] < 0, r.w = v.size() - 1, head.erase(head.begin());
	for (i = 0; i != head.size(); ++i)
		if (head[i] < 0) hvars.emplace(head[i], i); // var
		else for (b = 0; b != bits; ++b)
			r.hsym = bdd_and(r.hsym, from_bit(BIT(0, i), head[i]&(1<<b)));
	map<K, array<size_t, 2>> m;
	if (v.size()==1) return r.h = r.hsym, r;
	const size_t vars = ((r.w+1)*bits+1)*(ar+2);
	r.hvars = new size_t[vars];
	r.x = new bool[vars];
	for (i = 0; i < vars; ++i) r.x[i] = false, r.hvars[i] = i;
	for (i = 0; i != v.size()-1; ++i, r.h = bneg ? bdd_and_not(r.h, k) : bdd_and(r.h, k))
		for (k = T, bneg = (v[i][0]<0), v[i].erase(v[i].begin()), j=0; j != v[i].size(); ++j)
			from_arg(i, j, k, v[i][j], bits, ar, hvars, m, r, npad);
	r.h = bdd_and_not(r.h, npad);
	return r;
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K>
bool dict_t<K>::dictcmp::operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const{
	if (x.second != y.second) return x.second < y.second;
	return wcsncmp(x.first, y.first, x.second) < 0;
}

template<typename K> K dict_t<K>::operator()(wstr s, size_t len) {
	if (*s == L'?') {
		auto it = vars_dict.find({s, len});
		if (it != vars_dict.end()) return it->second;
		K r = -vars_dict.size() - 1;
		return vars_dict[{s, len}] = r;
	}
	auto it = syms_dict.find({s, len});
	if (it != syms_dict.end()) return it->second;
	return syms.push_back(s), lens.push_back(len), syms_dict[{s,len}] = syms.size() - 1;
}

template<typename K> K lp<K>::str_read(wstr *s) {
	wstr t;
	while (**s && iswspace(**s)) ++*s;
	if (!**s) throw runtime_error("identifier expected");
	if (*(t = *s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == *s) throw runtime_error("identifier expected");
	K r = dict(*s, t - *s);
	while (*t && iswspace(*t)) ++t;
	return *s = t, r;
}

template<typename K> vector<K> lp<K>::term_read(wstr *s) {
	vector<K> r;
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

template<typename K> matrix<K> lp<K>::rule_read(wstr *s) {
	vector<K> t;
	matrix<K> r;
	if ((t = term_read(s)).empty()) return r;
	r.push_back(t);
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	while (iswspace(**s)) ++*s;
	if (*((*s)++) != L':' || *((*s)++) != L'-') er(sep_expected);
loop:	if ((t = term_read(s)).empty()) er("term expected");
	r.insert(r.end()-1, t); // make sure head is last
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	goto loop;
}

template<typename K> void lp<K>::prog_read(wstr s) {
	vector<matrix<K>> r;
	db = bdds::F;
	size_t l;
	ar = maxw = 0;
	for (matrix<K> t; !(t = rule_read(&s)).empty(); r.push_back(t))
		for (const vector<K>& x : t) // we really support a single rel arity
			ar = max(ar, x.size()-1); // so we'll pad everything
	for (matrix<K>& x : r)
		for (vector<K>& y : x)
			if ((l=y.size()) < ar+1)
				y.resize(ar+1), fill(y.begin()+l, y.end(), dict.pad); // the padding
	bits = dict.bits();
	pdbs = new bdds(ar * bits), pprog = new bdds(maxw * ar * bits);
	for (const matrix<K>& x : r)
	 	if (x.size() == 1) db = pdbs->bdd_or(db, pdbs->from_rule(x, bits, ar).h);// fact
		else {
			rules.push_back(pprog->from_rule(x, bits, ar)); // rule
			out<K>(wcout<<"from_rule: ", *pprog, rules.back().h, bits, ar * rules.back().w, dict) << endl;
			out<K>(wcout<<"hsym: ", *pprog, rules.back().hsym, bits, ar, dict) << endl;
		}
	for (const rule& x : rules) maxw = max(maxw, x.w);
}

template<typename K> void lp<K>::step() {
	size_t add = bdds::F, del = bdds::F, s, x, y, z;
	wcout << endl;
	bdds &dbs = *pdbs, &prog = *pprog;
	for (const rule& r : rules) { // per rule
		int_t root = dbs.setpow(db, r.w, maxw);
		if (bdds::leaf(db)) {
			x = bdds::trueleaf(db) ? r.h : bdds_base::F;
			y = bdds::apply(prog, x, prog, op_exists(r.x, ((r.w+1)*bits+1)*(ar+2))); // remove nonhead variables
			z = prog.permute(y, r.hvars, ((r.w+1)*bits+1)*(ar+2)); // reorder the remaining vars
		} else  z = bdds::apply_and_ex_perm(dbs, root, prog, r.h, r.x, r.hvars, ((r.w+1)*bits+1)*(ar+2)); // rule/db conjunction
		z = prog.bdd_and(z, r.hsym);
		dbs.setpow(db, 1, maxw);
		(r.neg ? del : add) = bdds::apply_or(prog, z, dbs, r.neg ? del : add);
	}
	if ((s = dbs.bdd_and_not(add, del)) == bdds::F && add != bdds::F) db = bdds::F; // detect contradiction
	else db = dbs.bdd_or(dbs.bdd_and_not(db, del), s);// db = (db|add)&~del = db&~del | add&~del
	dbs.memos_clear();
	prog.memos_clear();
}

template<typename K> bool lp<K>::pfp() {
	size_t d, t = 0;
	for (set<int_t> s;;) {
		s.emplace(d = db);
		/*printdb*/(wcout<<"step: "<<++t<<" nodes: "<<pdbs->size()<<" + "<<pprog->size()<<endl);
		step();
		//printdb(wcout<<"after step: " << t << endl);
		if (s.find(db) != s.end()) return printdb(wcout), d == db;
	}
}
////////////////////////////////////////////////////////////////////////////////////////////////////
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
size_t std::hash<memo>::operator()(const memo& m) const {
	return (size_t)get<0>(m) + (size_t)get<1>(m) + (size_t)get<2>(m);
}
size_t std::hash<exmemo>::operator()(const exmemo& m) const {
	return (size_t)get<0>(m) + (size_t)get<1>(m) + (size_t)get<2>(m) + (size_t)get<3>(m);
}
size_t std::hash<pair<const bdds*, size_t>>::operator()(const pair<const bdds*, size_t>& m) const {
	return (size_t)m.first + m.second;
}
////////////////////////////////////////////////////////////////////////////////////////////////////
int main() {
	setlocale(LC_ALL, "");
	lp<int32_t> p;
	wstring s = file_read_text(stdin); // got to stay in memory
	p.prog_read(s.c_str());
	if (!p.pfp()) wcout << "unsat" << endl;
	return 0;
}
