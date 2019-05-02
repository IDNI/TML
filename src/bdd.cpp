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
#include "term.h"
//#define MEMO
using namespace std;

int_t onmemo(int_t n) {
//	dump_stack();
	static int_t memos = 0;
	return memos += n;
}
spbdd T, F;
size_t bdd::gc = 0;

map<sizes, unordered_map<spbdd, spbdd>> memos_perm;
map<bools, unordered_map<spbdd, spbdd>> memos_ex;
map<pair<sizes, bools>, unordered_map<spbdd, spbdd>> memos_perm_ex;
map<bdds, spbdd> memo_and_many;
map<bdds, spbdd> memo_or_many;
typedef array<spbdd, 2> memo;
template<> struct std::hash<memo> {
	size_t operator()(const memo& m) const {
		return (size_t)m[0].get() + (size_t)m[1].get();
	}
};
unordered_map<memo, spbdd> memo_and, memo_and_not, memo_or, memo_dt;
#ifdef MEMO
typedef pair<bools, size_t> exmemo;
typedef pair<bools, memo> apexmemo;
typedef pair<sizes, size_t> permemo;
template<> struct std::hash<exmemo> { size_t operator()(const exmemo&m)const;};
template<>struct std::hash<apexmemo>{size_t operator()(const apexmemo&m)const;};
template<> struct std::hash<permemo>{ size_t operator()(const permemo&m)const;};
//unordered_map<memo, spbdd, array_hash<spbdd, 2>> memo_and, memo_and_not, memo_or, memo_dt;
unordered_map<memo, spbdd> memo_and, memo_and_not, memo_or, memo_dt;
#define apply_ret(r, m) return onmemo(), m.emplace(t, res = (r)), res
#else
#define apply_ret(r, m) return r
#endif

unordered_map<bdd::key, weak_ptr<bdd>, bdd::keyhash> bdd::M; // bdd to its ptr
bool bdd::onexit = false;

void allsat_cb::sat(spbdd x) {
	if (x->leaf() && !x->trueleaf()) return;
	else if (!x->leaf() && v < x->v()) {
		DBG(assert(x->v() <= nvars);)
		p[++v-2] = true, sat(x), p[v-2] = false, sat(x), --v;
	} else if (v != nvars + 1)
		p[++v-2] = true, sat(x->h()),
		p[v-2] = false, sat(x->l()), --v;
	else f(p, x);
}

void sat(size_t v, size_t nvars, spbdd x, bools& p, vbools& r) {
	if (x->leaf() && !x->trueleaf()) return;
	if (!x->leaf() && v < x->v())
		p[v-1] = true,  sat(v + 1, nvars, x, p, r),
		p[v-1] = false, sat(v + 1, nvars, x, p, r);
	else if (v != nvars+1)
		p[v-1] = true,  sat(v + 1, nvars, x->h(), p, r),
		p[v-1] = false, sat(v + 1, nvars, x->l(), p, r);
	else	r.push_back(p);
}

vbools allsat(spbdd x, size_t nvars) {
	bools p(nvars);
	vbools r;
	return sat(1, nvars, x, p, r), r;
}

/*vbools allsat(spbdd x, size_t bits, size_t args) {
	vbools v = allsat(x, bits * args), s;
	for (bools b : v) {
		s.emplace_back(bits*args);
		for (size_t n = 0; n != bits; ++n)
			for (size_t k = 0; k != args; ++k)
				s.back()[k*bits+n] = b[POS(n,bits,k,args)];
	}
	return s;
}*/

spbdd bdd_or(const spbdd& x, const spbdd& y) {
	if (x == y || y == F) return x;
	if (x == F) return y;
	if (x == T || y == T) return T;
	const size_t &vx = x->v(), &vy = y->v();
	size_t v;
	spbdd a = x->h(), b = y->h(), c = x->l(), d = y->l();
	if (!leafvar(vy) && (leafvar(vx) || vx > vy)) a = c = x, v = vy;
	else if (leafvar(vx)) return a==T||b==T ? T : F;
	else if ((v = vx) < vy || leafvar(vy)) b = d = y;
	DBG(assert(!leafvar(v));)
	return bdd::add(v, bdd_or(a, b), bdd_or(c, d));
}

spbdd operator||(const spbdd& x, const spbdd& y) {
	if (x == y || y == F) return x;
	if (x == F) return y;
	if (x == T || y == T) return T;
//	return bdd_or(x, y);
	memo t = {{x, y}};
	auto it = memo_or.find(t);
	if (it != memo_or.end()) return it->second;
	return memo_or[t] = bdd_or(x, y);
}

spbdd bdd_ex(spbdd x, const bools& b, unordered_map<spbdd, spbdd>& memo) {
	if (x->leaf()) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	spbdd r;
	while (x->v()-1 < b.size() && b[x->v()-1]) {
		r = x->h() || x->l();
		if (r->leaf()) return onmemo(), memo.emplace(x, r), r;
		x = r;
	}
	if (x->v()-1 >= b.size()) return x;
	DBG(assert(x->v()-1 < b.size()));
	onmemo();
	return memo.emplace(x, bdd::add(x->v(), bdd_ex(x->h(), b, memo),
				bdd_ex(x->l(), b, memo))).first->second;
//	apply_ret(bdd::add({{n.v, bdd_ex(n.h, b), bdd_ex(n.l, b)}}), memo_ex);
}

spbdd operator/(spbdd x, const bools& b) { return bdd_ex(x, b, memos_ex[b]); }

spbdd bdd_permute(spbdd x, const sizes& m, unordered_map<spbdd, spbdd>& memo) {
	if (x->leaf()) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	onmemo();
	return memo.emplace(x, bdd_ite(m[x->v()-1], bdd_permute(x->h(), m,memo),
		bdd_permute(x->l(), m, memo))).first->second;
}

spbdd operator^(spbdd x, const sizes& m) {
	return bdd_permute(x, m, memos_perm[m]);
}

spbdd bdd_permute_ex(spbdd x, const bools& b, const sizes& m, size_t last,
	unordered_map<spbdd, spbdd>& memo) {
	if (x->leaf() || x->v() > last+1) return x;
	spbdd t = x;
	DBG(assert(b.size() >= x->v());)
	for (spbdd r; x->v()-1 < b.size() && b[x->v()-1]; x = r)
		if ((r = (x->h() || x->l()))->leaf()) return r;
		DBG(else assert(b.size() >= r->v());)
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	onmemo();
	DBG(assert(!x->leaf() && m.size() >= x->v());)
	return	memo.emplace(t, bdd_ite(m[x->v()-1],
		bdd_permute_ex(x->h(), b, m, last, memo),
		bdd_permute_ex(x->l(), b, m, last, memo))).first->second;
}

spbdd bdd_permute_ex(spbdd x, const bools& b, const sizes& m) {
//	DBG(assert(bdd_nvars(x) <= b.size());)
//	DBG(assert(bdd_nvars(x) <= m.size());)
	size_t last = 0;
	for (size_t n = 0; n != b.size(); ++n) if (b[n] || m[n] != n) last = n;
	return bdd_permute_ex(x, b, m, last, memos_perm_ex[{m,b}]);
}

spbdd bdd_and(spbdd x, spbdd y) {
	if (x == y || y == T) return x;
	if (x == T) return y;
	if (x == F || y == F) return F;
	const size_t &vx = x->v(), &vy = y->v();
	size_t v;
	spbdd a = x->h(), b = y->h(), c = x->l(), d = y->l();
	if ((leafvar(vx) && !leafvar(vy)) || (!leafvar(vy) && (vx > vy)))
		a = c = x, v = vy;
	else if (leafvar(vx)) return a==T&&b==T?T:F;
	else if ((v = vx) < vy || leafvar(vy)) b = d = y;
	return bdd::add(v, bdd_and(a, b), bdd_and(c, d));
}

spbdd operator&&(spbdd x, spbdd y) {
	if (x == y || y == T) return x;
	if (x == T) return y;
	if (x == F || y == F) return F;
//#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_and.find(t);
	if (it != memo_and.end()) return it->second;
	spbdd res;
//#endif
	const size_t &vx = x->v(), &vy = y->v();
	size_t v;
	spbdd a = x->h(), b = y->h(), c = x->l(), d = y->l();
	if ((leafvar(vx) && !leafvar(vy)) || (!leafvar(vy) && (vx > vy)))
		a = c = x, v = vy;
	else if (leafvar(vx)) apply_ret((a==T&&b==T)?T:F, memo_and);
	else if ((v = vx) < vy || leafvar(vy)) b = d = y;
	return onmemo(), memo_and.emplace(t,
		res = bdd::add(v, a && b, c && d)), res;
//	apply_ret(bdd::add(v, a && b, c && d), memo_and);
}

/*spbdd operator&&(spbdd x, spbdd y) {
	if (x == y || y == T) return x;
	if (x == T) return y;
	if (x == F || y == F) return F;
//	return bdd_and(x, y);
	memo t = {{x, y}};
	auto it = memo_and.find(t);
	if (it != memo_and.end()) return it->second;
	return memo_and[t] = bdd_and(x, y);
}*/

spbdd operator%(spbdd x, spbdd y) {
	if (x == y || x == F || y == T) return F;
#ifdef MEMO
	memo t = {{x, y}};
	auto it = memo_and_not.find(t);
	if (it != memo_and_not.end()) return it->second;
	spbdd res;
#endif
	const size_t &vx = x->v(), &vy = y->v();
	size_t v;
	spbdd a = x->h(), b = y->h(), c = x->l(), d = y->l();
	if ((leafvar(vx) && !leafvar(vy)) || (!leafvar(vy) && (vx > vy)))
		a = c = x, v = vy;
	else if (leafvar(vx)) apply_ret((a==T&&b==F)?T:F, memo_and_not);
	else if ((v = vx) < vy || leafvar(vy)) b = d = y;
	apply_ret(bdd::add(v, a%b, c%d),memo_and_not);
}

/*spbdd bdd_expand(spbdd x, size_t args1, size_t args2, size_t bits) {
	if (args1 == args2) return x;
	DBG(assert(args1 < args2);)
	sizes perm(args1 * bits);
	size_t n;
	for (n = 0; n != args1 * bits; ++n) perm[n] = n;
	for (n = 0; n != args1; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[POS(k, bits, n, args1)] = POS(k, bits, n, args2);
	return x ^ perm;
}

pair<bools, sizes> bdd_subterm(size_t from, size_t to, size_t args1,
	size_t args2, size_t bits) {
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
	return {ex, perm};
}

spbdd bdd_subterm(spbdd x, const bools& ex, const sizes& perm, size_t from,
	size_t to, size_t args1) {
	if (args1 == to - from) return from ? F : x;
	return bdd_permute_ex(x, ex, perm);// (x / ex) ^ perm;
}

spbdd bdd_subterm(spbdd x, size_t from, size_t to, size_t args1, size_t args2,
	size_t bits) {
	auto y = bdd_subterm(from, to, args1, args2, bits);
	return bdd_subterm(x, y.first, y.second, from, to, args1);
}*/

//spbdd bdd_deltail(spbdd x, size_t args1, size_t args2, size_t bits) {
//	return bdd_subterm(x, 0, args2, args1, args2, bits);
//}

/*size_t bdd_deltail(size_t x, size_t h) {
	if (leaf(x)) return x;
#ifdef MEMO
	memo t = {{x, h}};
	auto it = memo_dt.find(t);
	if (it != memo_dt.end()) return it->second;
	size_t res;
#endif
	bdd n = getbdd(x);
	if (n.v <= h)
		apply_ret(bdd::add({{n.v, bdd_deltail(n.h,h),
			bdd_deltail(n.l,h)}}), memo_dt);
	apply_ret(n.h == F && n.l == F ? F : T, memo_dt);
}
*/
size_t bdd_and_many_iter(bdds v, bdds& h, bdds& l, spbdd &res, size_t &m) {
	size_t i;
	spbdd t;
	bool b, eq, flag;
	bdds x;
	if (v.empty()) return res = T, 1;
	if (v.size() == 2) return res=v[0]&&v[1],1;
	for (size_t n = 0; n < v.size();)
		if (!v[n]->leaf()) ++n;
		else if (!v[n]->trueleaf()) return res = F, 1;
		else if (v.erase(v.begin()+n), v.size()==1) return res=v[0], 1;
		else if (v.size() == 2) return res=v[0]&&v[1],1;
		else if (v.empty()) return res = T, 1;
		else ++n;
	m = v[0]->v(), t = v[0];
	b = false, eq = true, flag = false;
	for (i = 1; i != v.size(); ++i)
		if (!v[i]->leaf()) {
			b |= v[i]->v() != m, eq &= t == v[i];
			if (v[i]->v() < m) m = v[i]->v();
		} else if (!v[i]->trueleaf()) return res = F, 1;
	if (eq) return res = t, 1;
	for (i = 0; i != v.size(); ++i)
		if (b && v[i]->v() != m) h.push_back(v[i]);
		else if (!v[i]->h()->leaf()) h.push_back(v[i]->h());
		else if (!v[i]->h()->trueleaf()) { flag = true; break; }
	for (i = 0; i != v.size(); ++i)
		if (b && v[i]->v() != m) l.push_back(v[i]);
		else if (!v[i]->l()->leaf()) l.push_back(v[i]->l());
		else if (!v[i]->l()->trueleaf()) return flag ? res=F,1 : 2;
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
	set_intersection(h.begin(),h.end(),l.begin(),l.end(),back_inserter(x));
	if (x.size() > 1) {
		for (size_t n = 0; n < h.size();)
			if (hasb(x, h[n])) h.erase(h.begin() + n);
			else ++n;
		for (size_t n = 0; n < l.size();)
			if (hasb(x, l[n])) l.erase(l.begin() + n);
			else ++n;
		spbdd r = bdd_and_many(move(x));
		if (r == F) return res = F, 1;
		h.push_back(r), l.push_back(r);
	}
	return 0;
}

spbdd bdd_and_many(bdds v) {
	if (v.empty()) return T;
	if (v.size() == 1) return v[0];
#ifdef MEMO
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
#endif
	//bdd::validate();
	auto it = memo_and_many.find(v);
	if (it != memo_and_many.end()) return it->second;
	it = memo_and_many.emplace(v, nullptr).first;
	onmemo();
	spbdd res = F, h, l;
	size_t m = 0;
	bdds vh, vl;
	switch (bdd_and_many_iter(move(v), vh, vl, res, m)) {
		case 0: l = bdd_and_many(move(vl)),
			h = bdd_and_many(move(vh));
			break;
		case 1: return it->second = res;
		case 2: h = bdd_and_many(move(vh)), l = F; break;
		case 3: h = F, l = bdd_and_many(move(vl)); break;
		default: throw 0;
	}
	return it->second = bdd::add(m, h, l);
}

size_t bdd_or_many_iter(bdds v, bdds& h, bdds& l, spbdd &res, size_t &m) {
	size_t i;
	spbdd t;
	bool b, eq, flag;
	bdds x;
	if (v.empty()) return res = F, 1;
	if (v.size() == 2) return res=v[0]||v[1],1;
	for (size_t n = 0; n < v.size();)
		if (!v[n]->leaf()) ++n;
		else if (v[n]->trueleaf()) return res = T, 1;
		else if (v.erase(v.begin()+n), v.size()==1) return res=v[0], 1;
		else if (v.size() == 2) return res=v[0]||v[1],1;
		else if (v.empty()) return res = F, 1;
		else ++n;
	m = v[0]->v(), t = v[0];
	b = false, eq = true, flag = false;
	for (i = 1; i != v.size(); ++i)
		if (!v[i]->leaf()) {
			b |= v[i]->v() != m, eq &= t == v[i];
			if (v[i]->v() < m) m = v[i]->v();
		} else if (v[i]->trueleaf()) return res = T, 1;
	if (eq) return res = t, 1;
	for (i = 0; i != v.size(); ++i)
		if (b && v[i]->v() != m) h.push_back(v[i]);
		else if (!v[i]->h()->leaf()) h.push_back(v[i]->h());
		else if (v[i]->h()->trueleaf()) { flag = true; break; }
	for (i = 0; i != v.size(); ++i)
		if (b && v[i]->v() != m) l.push_back(v[i]);
		else if (!v[i]->l()->leaf()) l.push_back(v[i]->l());
		else if (v[i]->l()->trueleaf()) return flag ? res=T,1 : 2;
	sort(h.begin(), h.end()), sort(l.begin(), l.end());
	if (!flag) {
		for (size_t n = 1; n < h.size();)
			if (h[n] == h[n-1]) {
				h.erase(h.begin() + n);
//				if (h.empty()) { flag = true; break; }
				if (h.size() == 1) break;
			} else ++n;
	}
	for (size_t n = 1; n < l.size();)
		if (l[n] == l[n-1]) {
			l.erase(l.begin() + n);
//			if (l.empty()) return flag ? 3 : 0;
			if (l.size() == 1) break;
		} else ++n;
	if (flag) return 3;
	set_intersection(h.begin(),h.end(),l.begin(),l.end(),back_inserter(x));
	if (x.size() > 1) {
		for (size_t n = 0; n < h.size();)
			if (hasb(x, h[n])) h.erase(h.begin() + n);
			else ++n;
		for (size_t n = 0; n < l.size();)
			if (hasb(x, l[n])) l.erase(l.begin() + n);
			else ++n;
		spbdd r = bdd_or_many(move(x));
		if (r == T) return res = T, 1;
		h.push_back(r), l.push_back(r);
	}
	return 0;
}

spbdd bdd_or_many(bdds v) {
	if (v.empty()) return F;
	if (v.size() == 1) return v[0];
#ifdef MEMO
	auto jt = memo_or.end();
	for (size_t n = 0; n < v.size(); ++n)
		for (size_t k = 0; k < n; ++k) {
			if ((jt=memo_or.find({v[n], v[k]})) == memo_or.end())
				jt=memo_or.find({v[k], v[n]});
			if (jt != memo_or.end()) {
				v.erase(v.begin() + k), v.erase(v.begin()+n-1),
				v.push_back(jt->second), n = k = 0; break;
			}
		}
#endif
	auto it = memo_or_many.find(v);
	if (it != memo_or_many.end()) return it->second;
	it = memo_or_many.emplace(v, nullptr).first;
	onmemo();
	spbdd res = F, h, l;
	size_t m = 0;
	bdds vh, vl;
	switch (bdd_or_many_iter(move(v), vh, vl, res, m)) {
		case 0: l = bdd_or_many(move(vl)),
			h = bdd_or_many(move(vh));
			break;
		case 1: return it->second = res;
		case 2: h = bdd_or_many(move(vh)), l = T; break;
		case 3: h = T, l = bdd_or_many(move(vl)); break;
		default: throw 0;
	}
	return it->second = bdd::add(m, h, l);
}

spbdd bdd_ite(size_t v, spbdd t, spbdd e) {
	DBG(assert(!leafvar(v+1));)
	if ((t->leaf() || v < t->v()) && (e->leaf() || v < e->v()))
		return bdd::add(v+1, t, e);
	return (bdd::from_bit(v,true) && t) || (bdd::from_bit(v,false) && e);
}

size_t count(spbdd x, size_t nvars) {
//	bdd n = getbdd(x), k;
	size_t r = 0;
	if (x->leaf()) return x->trueleaf() ? 1 : 0;
//	k = getbdd(n.h);
	r += count(x->h(), nvars)*(1<<(((x->h()->leaf()?nvars+1-x->v():
			(x->h()->v()-x->v())))-1));
//	k = getbdd(n.l);
	r += count(x->l(), nvars)*(1<<(((x->l()->leaf()?nvars+1-x->v():
			(x->l()->v()-x->v())))-1));
	return r;
}

size_t bdd_count(spbdd x, size_t nvars) {
	return	x->leaf()?x->trueleaf()?(1<<(nvars)):0:
		(count(x, nvars)<<(x->v()-1));
}

bool bdd_onesat(spbdd x, size_t nvars, bools& r) {
	if (x->leaf()) return x->trueleaf();
	return	x->l()->leaf() && !x->l()->trueleaf()
		? r[x->v()-1] = true,  bdd_onesat(x->h(), nvars, r)
		:(r[x->v()-1] = false, bdd_onesat(x->l(), nvars, r));
}

/*spbdd from_int(size_t x, size_t bits, size_t arg, size_t args) {
	spbdd r = T;
	size_t b = bits;
	while (b--)
		r = r && bdd::from_bit(POS(b, bits, arg, args), x&(1<<b));
	return r;
}*/

size_t bdd_nvars(spbdd x) {
	if (x->leaf()) return 0;
	return max(max(x->v(), bdd_nvars(x->h())), bdd_nvars(x->l()));
}

#define print_memo_size(x) wcout << #x << ": " << x.size() << endl

void print_memos_len() {
	wcout<<"memos: "<<onmemo(0)<<endl;
#ifdef MEMO
	print_memo_size(memo_and);
	print_memo_size(memo_and_not);
	print_memo_size(memo_or);
#endif
	wcout<<"bdds: " << bdd::size() << endl;
}

void memos_clear() {
	for (auto x : memos_perm) onmemo(-x.second.size());//, x.second.clear();
	for (auto x : memos_ex) onmemo(-x.second.size());//, x.second.clear();
	for (auto x : memos_perm_ex)onmemo(-x.second.size());//,x.second.clear();
	memos_perm.clear(), memos_ex.clear(), memos_perm_ex.clear();
	onmemo(-memo_and_many.size() - memo_or_many.size());
	memo_and_many.clear(), memo_or_many.clear();
	memo_and.clear();
#ifdef MEMO
	onmemo(-memo_and.size() - memo_and_not.size() - memo_or.size());
	memo_and.clear(), memo_and_not.clear(), memo_or.clear();
#endif
}

void bdd::clear() { M.clear(); memos_clear(); init(); }

#ifdef MEMO
/*size_t std::hash<apexmemo>::operator()(const apexmemo& m) const {
	static std::hash<bools> h1;
	static array_hash<size_t, 2> h2;
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
}*/
#endif
