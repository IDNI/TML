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
#include <map>
#include <algorithm>
#include <cassert>
#include <cstring>
#include "bdd.h"

using namespace std;

template<> struct std::hash<node> {
	size_t operator()(const node& n) const { return n[0] + n[1] + n[2]; }
};

#define MEMO
#ifdef MEMO
typedef array<size_t, 2> memo;
typedef array<size_t, 3> adtmemo;
typedef pair<bools, size_t> exmemo;
typedef pair<bools, memo> apexmemo;
typedef pair<sizes, size_t> permemo;
template<> struct std::hash<memo> { size_t operator()(const memo& m) const; };
template<> struct std::hash<exmemo> { size_t operator()(const exmemo&m)const;};
template<>struct std::hash<apexmemo>{size_t operator()(const apexmemo&m)const;};
template<> struct std::hash<permemo>{ size_t operator()(const permemo&m)const;};
unordered_map<memo, size_t> memo_and, memo_and_not, memo_or, memo_dt;
unordered_map<adtmemo, size_t> memo_adt;
unordered_map<exmemo, size_t> memo_ex;
unordered_map<apexmemo, size_t> memo_and_ex, memo_and_not_ex;
unordered_map<permemo, size_t> memo_permute;
#define apply_ret(r, m) return m.emplace(t, res = (r)), res
#else
#define apply_ret(r, m) return r
#endif

vector<node> V; // all bdd nodes
unordered_map<node, size_t> M; // node to its index

size_t bdd_add_nocheck(const node& n) {
	size_t r;
	return M.emplace(n, r = V.size()), V.emplace_back(n), r;
}

void bdd_init() { bdd_add_nocheck({{0, 0, 0}}), bdd_add_nocheck({{0, 1, 1}}); }
//bool print = false;
size_t bdd_add(const node& n) { // create new bdd node,standard implementation
//	if (print) wcout << n << endl;
	if (n[1] == n[2]) return n[1];
#ifdef DEBUG	
	if (!leaf(n[1])) assert(n[0] < getnode(n[1])[0]);
	if (!leaf(n[2])) assert(n[0] < getnode(n[2])[0]);
#endif	
	auto it = M.find(n);
	return it == M.end() ? bdd_add_nocheck(n) : it->second;
}

void allsat_cb::sat(size_t v, const node& n) {
	if (nleaf(n) && !ntrueleaf(n)) return;
	if (v < n[0])
		p[v-1] = true,  sat(v + 1, n),
		p[v-1] = false, sat(v + 1, n);
	else if (v != nvars+1)
		p[v-1] = true,  sat(v + 1, getnode(n[1])),
		p[v-1] = false, sat(v + 1, getnode(n[2]));
	else	f(p);
}

void sat(size_t v, size_t nvars, node n, bools& p, vbools& r) {
	if (nleaf(n) && !ntrueleaf(n)) return;
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
	if (x == y) return x;
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_or.find(t);
	if (it != memo_or.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (nleaf(Vx)) apply_ret(ntrueleaf(Vx) ? T : y, memo_or);
       	const node &Vy = getnode(y);
	if (nleaf(Vy)) apply_ret(ntrueleaf(Vy) ? T : x, memo_or);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret(a||b ? T : F, memo_or);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_add({{v, bdd_or(a, b), bdd_or(c, d)}}), memo_or);
}

size_t bdd_ex(size_t x, const bools& b) {
	if (leaf(x)) return x;
	node n = getnode(x);
#ifdef MEMO
	exmemo t = {b, x};
	auto it = memo_ex.find(t);
	if (it != memo_ex.end()) return it->second;
	size_t res;
#endif	
	while (n[0]-1 < b.size() && b[n[0]-1]) {
		x = bdd_or(n[1], n[2]);
		if (leaf(x)) apply_ret(x, memo_ex);
		n = getnode(x);
	}
	if (n[0]-1 >= b.size()) return x;
	apply_ret(bdd_add({{n[0], bdd_ex(n[1], b), bdd_ex(n[2], b)}}), memo_ex);
}

size_t bdd_and(size_t x, size_t y) {
	if (x == y) return x;
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_and.find(t);
	if (it != memo_and.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (nleaf(Vx)) apply_ret(ntrueleaf(Vx)?y:F, memo_and);
       	const node &Vy = getnode(y);
	if (nleaf(Vy)) apply_ret(!ntrueleaf(Vy) ? F : x, memo_and);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret((a&&b)?T:F, memo_and);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_add({{v, bdd_and(a, b), bdd_and(c, d)}}), memo_and);
}

size_t bdd_and_not(size_t x, size_t y) {
	if (x == y) return F;
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_and_not.find(t);
	if (it != memo_and_not.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (nleaf(Vx) && !ntrueleaf(Vx)) apply_ret(F, memo_and_not);
       	const node &Vy = getnode(y);
	if (nleaf(Vy)) apply_ret(ntrueleaf(Vy) ? F : x, memo_and_not);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret((a&&!b)?T:F, memo_and_not);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_add({{v,bdd_and_not(a,b),bdd_and_not(c,d)}}),memo_and_not);
}

size_t bdd_expand(size_t x, size_t args1, size_t args2, size_t bits) {
	if (args1 == args2) return x;
	sizes perm(args1 * bits);
	size_t n;
	for (n = 0; n != args1 * bits; ++n) perm[n] = n;
	for (n = 0; n != args1; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[POS(k, bits, n, args1)] = POS(k, bits, n, args2);
	return bdd_permute(x, perm);
}

size_t bdd_subterm(size_t x, size_t from, size_t to, size_t args1, size_t args2,
	size_t bits) {
	if (args1 == to - from) return from ? F : x;
	bools ex(args1 * bits, false);
	sizes perm(args1 * bits);
	size_t n;
	for (n = 0; n != args1 * bits; ++n) perm[n] = n;
	for (n = 0; n != args1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n < from || n >= to)
				ex[POS(k, bits, n, args1)] = true;
			else perm[POS(k, bits, n, args1)] =
				POS(k, bits, n - from, args2);
	return bdd_permute(bdd_ex(x, ex), perm);
}

size_t bdd_deltail(size_t x, size_t args1, size_t args2, size_t bits) {
	return bdd_subterm(x, 0, args2, args1, args2, bits);
	if (args1 == args2) return x;
	bools ex(args1 * bits, false);
	sizes perm(args1 * bits);
	assert(args1 > args2);
	size_t n;
	for (n = 0; n != args1 * bits; ++n) perm[n] = n;
	for (n = 0; n != args1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n >= args2) ex[POS(k, bits, n, args1)] = true;
			else perm[POS(k,bits,n,args1)] = POS(k,bits,n,args2);
	return bdd_permute(bdd_ex(x, ex), perm);
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
	if (x == y) return bdd_deltail(x, h);
#ifdef MEMO
	adtmemo t = {{x, y, h}};
	auto it = memo_adt.find(t);
	if (it != memo_adt.end()) return it->second;
	size_t res;
#endif	
	const node &Vx = getnode(x);
	if (nleaf(Vx)) apply_ret(ntrueleaf(Vx)?bdd_deltail(y, h):F, memo_adt);
       	const node &Vy = getnode(y);
	if (nleaf(Vy)) apply_ret(!ntrueleaf(Vy)?F:bdd_deltail(x, h),memo_adt);
	const size_t &vx = Vx[0], &vy = Vy[0];
	size_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) apply_ret((a&&b)?T:F, memo_adt);
	else if ((v = vx) < vy || !vy) b = d = y;
	apply_ret(bdd_deltail(bdd_add({{v, bdd_and_deltail(a, b, h),
		bdd_and_deltail(c, d, h)}}), h), memo_adt);
}

size_t bdd_and_many_iter(sizes v, sizes& h, sizes& l, size_t &res, size_t &m) {
	size_t i, t;
	bool b, eq, flag;
	if (v.empty()) return T;
	for (size_t n = 0; n < v.size();) {
		if (leaf(v[n])) {
			if (!trueleaf(v[n])) return F;
			v.erase(v.begin() + n);
			if (v.size() == 1) return res = v[0], 1;
			else if (v.size() == 2) return res=bdd_and(v[0],v[1]),1;
			else if (v.empty()) return T;
			else ++n;
		} else ++n;
	}
	m = getnode(v[0])[0], t = v[0];
	b = false, eq = true, flag = false;
	for (i = 1; i != v.size(); ++i)
		if (!leaf(v[i])) {
			const node &n = getnode(v[i]);
			b |= n[0] != m, eq &= t == v[i];
			if (n[0] < m) m = n[0];
		} else if (!trueleaf(v[i])) return res = F, 1;
	if (eq) return res = t, 1;
	for (i = 0; i != v.size(); ++i)
		if (b && getnode(v[i])[0] != m) h.push_back(v[i]);
		else if (!leaf(getnode(v[i])[1])) h.push_back(getnode(v[i])[1]);
		else if (!trueleaf(getnode(v[i])[1])) { flag = true; break; }
	for (i = 0; i != v.size(); ++i)
		if (b && getnode(v[i])[0] != m) l.push_back(v[i]);
		else if (!leaf(getnode(v[i])[2])) l.push_back(getnode(v[i])[2]);
		else if (!trueleaf(getnode(v[i])[2])) return flag ? res=F,1 : 2;
	sort(h.begin(), h.end()), sort(l.begin(), l.end());
	if (!flag) { 
		for (size_t n = 1; n < h.size();)
			if (h[n] == h[n-1]) {
				h.erase(h.begin() + n);
				if (h.empty()) { flag = true; break; }
				if (h.size() == 1) break;
			} else ++n;
	}
	for (size_t n = 1; n < l.size();)
		if (l[n] == l[n-1]) {
			l.erase(l.begin() + n);
			if (l.empty()) return flag ? 3 : 0;
			if (l.size() == 1) break;
		} else ++n;
	if (flag) return 3;
	sizes x;
	set_intersection(h.begin(),h.end(),l.begin(),l.end(),back_inserter(x));
	if (x.size() > 1) {
		size_t r = bdd_and_many(x);
		for (size_t n = 0; n < h.size();)
			if (has(x, h[n])) h.erase(h.begin() + n);
			else ++n;
		for (size_t n = 0; n < l.size();)
			if (has(x, l[n])) l.erase(l.begin() + n);
			else ++n;
		h.push_back(r), l.push_back(r);
	}
	return 0;
}

size_t bdd_and_many(sizes v) {
	static map<sizes, size_t> memo;
	auto jt = memo_and.end();

	for (size_t n = 0; n < v.size(); ++n)
		for (size_t k = 0; k < n; ++k) {
			if ((jt=memo_and.find({v[n], v[k]})) == memo_and.end())
				jt=memo_and.find({v[k], v[n]});
			if (jt != memo_and.end()) {
				v.erase(v.begin() + k), v.erase(v.begin()+n-1),
				v.push_back(jt->second), n = k = 0; break;
			}
		}
	auto it = memo.find(v);
	if (it != memo.end()) return it->second;
	it = memo.emplace(v, 0).first;
	size_t res = F, m = 0, h, l;
	sizes vh, vl;
	switch (bdd_and_many_iter(move(v), vh, vl, res, m)) {
		case 0: l = bdd_and_many(move(vl)),
			h = bdd_and_many(move(vh));
			break;
		case 1: return it->second = res;
		case 2: h = bdd_and_many(move(vh)), l = F; break;
		case 3: h = F, l = bdd_and_many(move(vl)); break;
		default: throw 0;
	}
	return it->second = bdd_add({{m, h, l}});
}

size_t bdd_ite(size_t v, size_t t, size_t e) {
	const node &x = getnode(t), &y = getnode(e);
	if ((nleaf(x)||v<x[0])&&(nleaf(y)||v<y[0])) return bdd_add({{v+1,t,e}});
	return bdd_or(bdd_and(from_bit(v,true),t),bdd_and(from_bit(v,false),e));
}

size_t bdd_permute(size_t x, const sizes& m) { //overlapping rename
#ifdef MEMO
	permemo t = {m, x};
	auto it = memo_permute.find(t);
	if (it != memo_permute.end()) return it->second;
	size_t res;
#endif	
	if (leaf(x)) return x;
	const node n = getnode(x);
	apply_ret(bdd_ite(m[n[0]-1], bdd_permute(n[1], m), bdd_permute(n[2],m)),
		memo_permute);
}

size_t count(size_t x, size_t nvars) {
	node n = getnode(x), k;
	size_t r = 0;
	if (nleaf(n)) return ntrueleaf(n) ? 1 : 0;
	k = getnode(n[1]);
	r += count(n[1], nvars)*(1<<(((nleaf(k)?nvars+1-n[0]:(k[0]-n[0])))-1));
	k = getnode(n[2]);
	r += count(n[2], nvars)*(1<<(((nleaf(k)?nvars+1-n[0]:(k[0]-n[0])))-1));
	return r;
}

size_t bdd_count(size_t x, size_t nvars) {
	return x<2?x?(1<<(nvars)):0:(count(x, nvars)<<(getnode(x)[0]-1));
}

bool bdd_onesat(size_t x, size_t nvars, bools& r) {
	if (leaf(x)) return trueleaf(x);
	node n = getnode(x);
	return	leaf(n[2]) && !trueleaf(n[2])
		? r[n[0]-1] = true,  bdd_onesat(n[1], nvars, r)
		:(r[n[0]-1] = false, bdd_onesat(n[2], nvars, r));
}

size_t from_int(size_t x, size_t bits, size_t arg, size_t args) {
	size_t r = T, b = bits;
	while (b--) r = bdd_and(r, from_bit(POS(b, bits, arg, args), x&(1<<b)));
	return r;
}

/*size_t bdd_rebit(size_t x, size_t prev, size_t curr, size_t nvars) {
	if (prev == curr) return x;
	assert(prev < curr);
	size_t t = T, n, k;
	sizes v(nvars);
	for (n = 0; n != nvars; ++n) {
		v[n] = (n % prev) + curr - prev + curr * (n / prev);
		for (k = 0; k != curr - prev; ++k)
			t = bdd_and(t, from_bit((n / prev) * curr + k, 0));
	}
	return bdd_and(t, bdd_permute(x, v));
}

void from_range(size_t max, size_t bits, size_t offset, size_t &r) {
	size_t x = F;
	for (size_t n = 0; n < max; ++n)
		x = bdd_or(x, from_int(n, bits, offset));
	r = bdd_and(r, x);
}

void from_range(size_t max, size_t bits, size_t offset, set<int_t> ex,
	size_t &r) {
	size_t x = F;
	for (size_t n = 0; n < max; ++n)
		if (ex.find(n) == ex.end())
			x = bdd_or(x, from_int(n, bits, offset));
	r = bdd_and(r, x);
}*/

void memos_clear() {
#ifdef MEMO		
	memo_and.clear(), memo_and_not.clear(), memo_or.clear(),
	memo_permute.clear(), memo_and_ex.clear(), memo_and_not_ex.clear();
#endif		
}

#ifdef MEMO
size_t std::hash<memo>::operator()(const memo& m) const { return m[0] + m[1]; }
size_t std::hash<apexmemo>::operator()(const apexmemo& m) const {
	static std::hash<bools> h1;
	static std::hash<memo> h2;
	return h1(m.first) + h2(m.second);
}
size_t std::hash<exmemo>::operator()(const exmemo& m) const {
	static std::hash<bools> h;
	return h(m.first) + (size_t)m.second;
}
size_t std::hash<permemo>::operator()(const permemo& m) const {
	size_t h = m.second;
	for (auto x : m.first) h += x;
	return h;
}
#endif
