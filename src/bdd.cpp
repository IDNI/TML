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
#include <cassert>
#include <algorithm>
#include "bdd.h"

#ifndef NOOUTPUTS
#include "output.h"
#define OUT(x) x
#else
#define OUT(x)
#endif

using namespace std;

#define MEMO
bool onexit = false;

template<typename T> struct veccmp {
	bool operator()(const vector<T>& x, const vector<T>& y) const{
		if (x.size() != y.size()) return x.size() < y.size();
		return x < y;
	}
};

template<typename T1, typename T2> struct vec2cmp {
	typedef pair<vector<T1>, vector<T2>> t;
	bool operator()(const t& x, const t& y) const {
		static veccmp<T1> t1;
		static veccmp<T2> t2;
		if (x.first != y.first) return t1(x.first, y.first);
		return t2(x.second, y.second);
	}
};

unordered_map<bdd_key, int_t> Ma;
bdd_mmap V;
bool gc_enabled = true; // Controls whether or not garbage collection is enabled
#ifndef NOMMAP
size_t max_bdd_nodes = 0;
mmap_mode bdd_mmap_mode = MMAP_NONE;
string bdd_mmap_file = "";
#endif
unordered_map<ite_memo, bdd_ref> C;
map<bools, unordered_map<array<bdd_ref, 2>, bdd_ref>, veccmp<bool>> CX;
map<pair<bools, uints>, unordered_map<array<bdd_ref, 2>, bdd_ref>,
	vec2cmp<bool, uint_t>> CXP;
unordered_map<bdds, bdd_ref> AM;
map<bools, unordered_map<bdds, bdd_ref>, veccmp<bool>> AMX;
map<pair<bools, uints>, unordered_map<bdds, bdd_ref>, vec2cmp<bool, uint_t>> AMXP;
unordered_set<int_t> S;
unordered_map<bdd_ref, weak_ptr<bdd_handle>> bdd_handle::M;
spbdd_handle htrue, hfalse;
map<bools, unordered_map<bdd_ref, bdd_ref>, veccmp<bool>> memos_ex;
map<uints, unordered_map<bdd_ref, bdd_ref>, veccmp<uint_t>> memos_perm;
map<pair<uints, bools>, unordered_map<bdd_ref, bdd_ref>, vec2cmp<uint_t, bool>>
	memos_perm_ex;

_Pragma("GCC diagnostic push")
_Pragma("GCC diagnostic ignored \"-Wstrict-overflow\"")
auto am_cmp = [](bdd_ref x, bdd_ref y) {
	bool s = x < y;
	x = x.abs(), y = y.abs();
	return x < y ? true : x == y ? s : false;
};
_Pragma("GCC diagnostic pop")

const size_t gclimit = 1e+6;

#ifndef NOMMAP
void bdd::init(mmap_mode m, size_t max_size, const string fn, bool gc) {
	gc_enabled = gc;
	bdd_mmap_mode = m;
	if ((max_bdd_nodes = max_size / sizeof(bdd)) < 2) max_bdd_nodes = 2;
	V = bdd_mmap(memory_map_allocator<bdd>(fn, m));
	if (m != MMAP_NONE) V.reserve(max_bdd_nodes);
#else
void bdd::init(bool gc) {
#endif
	//DBG(o::dbg() << "bdd::init(m: MMAP_" <<
	//	(m == MMAP_NONE ? "NONE" : "WRITE") <<
	//	", max_size: " << max_size << ", fn: " << fn
	//	<< ") max_bdd_nodes=" << max_bdd_nodes << "\n";)
	gc_enabled = gc;
	S.insert(0), S.insert(1), V.emplace_back(0, 0), // dummy
	V.emplace_back(1, 1),
	Ma.emplace(bdd_key(hash_pair(0, 0), 0, 0), 0),
	Ma.emplace(bdd_key(hash_pair(1, 1), 1, 1), 1),
	htrue = bdd_handle::get(T), hfalse = bdd_handle::get(F);
}

#ifndef NOMMAP
void bdd::max_bdd_size_check() {
	//DBG(o::dbg() << "add_check V.size()-1=" << V.size()-1
	//	<< " max_bdd_nodes=" << max_bdd_nodes << endl;)
	if (V.size() == max_bdd_nodes)
		CERR << "Maximum bdd size reached. Increase the limit"
		" with --bdd-max-size parameter. Exiting." << endl,
		onexit = true,
		exit(0);
		// TODO: offer user to remap instead of exit
}
#endif

bdd_ref bdd::add(int_t v, bdd_ref h, bdd_ref l) {
	DBG(assert(h.bdd_id && l.bdd_id && v > 0););
	if (h == l) return h;
	h = h.shift_var(-v);
	l = l.shift_var(-v);
	const bool inv_inp = h < l;
	if (inv_inp) swap(h, l);
	unordered_map<bdd_key, int_t>::const_iterator it;
	bdd_key k;
	const bool inv_out = l < 0;
	if (inv_out) { h = -h; l = -l; }
	std::hash<bdd_ref> hsh;
	k = bdd_key(hash_upair(hsh(h), hsh(l)), h, l);
	return	bdd_ref((it = Ma.find(k)) != Ma.end() ? it->second :
		(V.emplace_back(h, l),
		Ma.emplace(move(k), V.size()-1),
		V.size()-1), v, inv_inp, inv_out);
}

bdd_ref bdd::from_bit(uint_t b, bool v) {
	return v ? add(b + 1, T, F) : add(b + 1, F, T);
}

bool bdd::bdd_subsumes(const bdd_ref &x, const bdd_ref &y) {
	if (x == T) return true;
	if (x == F) return y == F;
	if (y == T) return false;
	if (y == F) return true;
	const bdd bx = get(x), by = get(y);
	if (x.shift < y.shift) return bdd_subsumes(bx.h, y) && bdd_subsumes(bx.l, y);
	if (x.shift > y.shift) return bdd_subsumes(x, by.h) && bdd_subsumes(x, by.l);
	return bdd_subsumes(bx.h, by.h) && bdd_subsumes(bx.l, by.l);
}

bdd_ref bdd::bdd_and(bdd_ref x, bdd_ref y) {
	DBG(assert(x.bdd_id && y.bdd_id);)
	if (x == F || y == F || x == -y) return F;
	if (x == T || x == y) return y;
	if (y == T) return x;
	if (x > y) swap(x, y);
	const bdd bx = get(x), by = get(y);
	ite_memo m = { x, y, F };
	bool leaf = 
		bx.h == T || bx.h == F || bx.l == T || bx.l == F ||
		by.h == T || by.h == F || by.l == T || by.l == F;
#ifdef MEMO
	if (!leaf && x.shift == y.shift)
		if (auto it = C.find(m); it != C.end())
			return it->second;
#endif
	if (x.shift < y.shift) return add(x.shift, bdd_and(bx.h, y), bdd_and(bx.l, y));
	if (x.shift > y.shift) return add(y.shift, bdd_and(x, by.h), bdd_and(x, by.l));
	bdd_ref r = add(x.shift, bdd_and(bx.h, by.h), bdd_and(bx.l, by.l));
#ifdef MEMO
	if (!leaf && C.size() < gclimit) C.emplace(m, r);
#endif
	return r;
}

bdd_ref bdd::bdd_ite_var(uint_t x, const bdd_ref &y, const bdd_ref &z) {
	if (x+1 < var(y) && x+1 < var(z)) return add(x+1, y, z);
	return bdd_ite(from_bit(x, true), y, z);
}

bdd_ref bdd::bdd_ite(const bdd_ref &x, const bdd_ref &y, const bdd_ref & z) {
	DBG(assert(x.bdd_id && y.bdd_id && z.bdd_id);)
	if (x < 0) return bdd_ite(-x, z, y);
	if (x == F) return z;
	if (x == T || y == z) return y;
	if (x == -y || x == z) return F;
	if (y == T) return bdd_or(x, z);
	if (y == F) return bdd_and(-x, z);
	if (z == F) return bdd_and(x, y);
	if (z == T) return bdd_or(-x, y);
	auto it = C.find({x, y, z});
	if (it != C.end()) return it->second;
	bdd_ref r;
	const bdd bx = get(x), by = get(y), bz = get(z);
	const int_t s = min(x.shift, min(y.shift, z.shift));
	if (x.shift == y.shift && y.shift == z.shift)
		r =	add(x.shift, bdd_ite(bx.h, by.h, bz.h),
				bdd_ite(bx.l, by.l, bz.l));
	else if (s == x.shift && s == y.shift)
		r =	add(x.shift, bdd_ite(bx.h, by.h, z),
				bdd_ite(bx.l, by.l, z));
	else if (s == y.shift && s == z.shift)
		r =	add(y.shift, bdd_ite(x, by.h, bz.h),
				bdd_ite(x, by.l, bz.l));
	else if (s == x.shift && s == z.shift)
		r =	add(x.shift, bdd_ite(bx.h, y, bz.h),
				bdd_ite(bx.l, y, bz.l));
	else if (s == x.shift)
		r =	add(x.shift, bdd_ite(bx.h, y, z), bdd_ite(bx.l, y, z));
	else if (s == y.shift)
		r =	add(y.shift, bdd_ite(x, by.h, z), bdd_ite(x, by.l, z));
	else	r =	add(z.shift, bdd_ite(x, y, bz.h), bdd_ite(x, y, bz.l));
	if (C.size() > gclimit) return r;
	return C.emplace(ite_memo{x, y, z}, r), r;
}

void am_sort(bdds& b) {
	sort(b.begin(), b.end(), am_cmp);
	for (size_t n = 0; n < b.size();)
		if (b[n] == T) b.erase(b.begin() + n);
		else if (b[n] == F) { b = {F}; return; }
		else if (!n) { ++n; continue; }
		else if (b[n] == b[n-1]) b.erase(b.begin() + n);
		else if (b[n] == -b[n-1]) { b = {F}; return; }
		else ++n;
}

size_t bdd::bdd_and_many_iter(bdds v, bdds& h, bdds& l, bdd_ref &res, size_t &m){
	size_t i;
	bool flag = false;
	m = var(v[0]);
	for (i = 1; i != v.size(); ++i)
		if (!leaf(v[i])) {
			if (var(v[i]) < m) m = var(v[i]);
		} else if (!trueleaf(v[i])) return res = F, 1;
	h.reserve(v.size()), l.reserve(v.size());
	for (i = 0; i != v.size(); ++i)
		if (var(v[i]) != m) h.push_back(v[i]);
		else if (!leaf(hi(v[i]))) h.push_back(hi(v[i]));
		else if (!trueleaf(hi(v[i]))) { flag = true; break; }
	if (!flag) am_sort(h);
	for (i = 0; i != v.size(); ++i)
		if (var(v[i]) != m) l.push_back(v[i]);
		else if (!leaf(lo(v[i]))) l.push_back(lo(v[i]));
		else if (!trueleaf(lo(v[i]))) return flag ? res = F, 1 : 2;
	am_sort(l);
	if (!flag) { if (h.size() && h[0] == F) flag = true; }
	if (l.size() && l[0] == F) return flag ? 3 : 2;
	if (flag) return 3;
	bdds x;
	set_intersection(h.begin(),h.end(),l.begin(),l.end(),back_inserter(x),
			am_cmp);
	am_sort(x);
	if (x.size() > 1) {
		for (size_t n = 0; n < h.size();)
			if (hasbc(x, h[n], am_cmp)) h.erase(h.begin() + n);
			else ++n;
		for (size_t n = 0; n < l.size();)
			if (hasbc(x, l[n], am_cmp)) l.erase(l.begin() + n);
			else ++n;
		h.shrink_to_fit(), l.shrink_to_fit(), x.shrink_to_fit();
		bdd_ref r = bdd_and_many(move(x));
		if (r == F) return res = F, 1;
		if (r != T) {
			if (!hasbc(h, r, am_cmp)) h.push_back(r), am_sort(h);
			if (!hasbc(l, r, am_cmp)) l.push_back(r), am_sort(l);
		}
	}
	return 0;
}

bool subset(const bdds& small, const bdds& big) {
	if (	big.size() < small.size() ||
		am_cmp(big[big.size()-1].abs(), small[0].abs()) ||
		am_cmp(small[small.size()-1].abs(), big[0].abs()))
		return false;
	for (const bdd_ref& t : small) if (!hasbc(big, t, am_cmp)) return false;
	return true;
}

size_t simps = 0;

bool bdd::am_simplify(bdds& v, const unordered_map<bdds, bdd_ref>& memo) {
	am_sort(v);
	for (auto x : memo)
		if (subset(x.first, v)) {
			if (x.second == F) return v={F}, true;
			for (size_t n = 0; n < v.size();)
				if (!hasbc(x.first, v[n], am_cmp)) ++n;
				else v.erase(v.begin() + n);
			if (!hasbc(v, x.second, am_cmp)) v.push_back(x.second);
			return true;
		}
	return false;
}

bdd_ref bdd::bdd_and_many(bdds v) {
#ifdef MEMO
	static unordered_map<ite_memo, bdd_ref>::const_iterator jt;
	for (size_t n = 0; n < v.size(); ++n)
		for (size_t k = 0; k < n; ++k) {
			bdd_ref x, y;
			if (v[n] < v[k]) x = v[n], y = v[k];
			else x = v[k], y = v[n];
			if ((jt = C.find({x, y, F})) != C.end()) {
				v.erase(v.begin()+k), v.erase(v.begin()+n-1),
				v.push_back(jt->second), n = k = 0;
				break;
			}
		}
#endif
	if (v.empty()) return T;
	if (v.size() == 1) return v[0];
	simps = 0;
	static bdds v1;
	do {
		if (v1=v, am_simplify(v, AM), ++simps, v.size()==1) return v[0];
	} while (v1 != v);
	if (v.empty()) return T;
	if (v.size() == 1) return v[0];
	auto it = AM.find(v);
	if (it != AM.end()) return it->second;
	if (v.size() == 2)
		return AM.emplace(v, bdd_and(v[0], v[1])).first->second;
	bdd_ref res = F, h, l;
	size_t m = 0;
	bdds vh, vl;
	switch (bdd_and_many_iter(v, vh, vl, res, m)) {
		case 0: l = bdd_and_many(move(vl)),
			h = bdd_and_many(move(vh));
			break;
		case 1: return AM.emplace(v, res), res;
		case 2: h = bdd_and_many(move(vh)), l = F; break;
		case 3: h = F, l = bdd_and_many(move(vl)); break;
		default: { DBGFAIL; return 0; }
	}
	return AM.emplace(v, bdd::add(m, h, l)).first->second;
}

bdd_ref bdd::bdd_and_ex(bdd_ref x, bdd_ref y, const bools& ex,
	unordered_map<array<bdd_ref, 2>, bdd_ref>& memo,
	unordered_map<bdd_ref, bdd_ref>& m2, int_t last) {
	DBG(assert(x.bdd_id && y.bdd_id);)
	if (x == F || y == F || x == -y) return F;
	if (x == T || x == y) return bdd_ex(y, ex, m2, last);
	if (y == T) return bdd_ex(x, ex, m2, last);
	if (x > y) swap(x, y);
	array<bdd_ref, 2> m = {x, y};
	auto it = memo.find(m);
	if (it != memo.end()) return it->second;
	const bdd bx = get(x), by = get(y);
	int_t v;
	bdd_ref rx, ry, r;
	if (x.shift > last+1 && y.shift > last+1)
		return memo.emplace(m, r = bdd_and(x, y)), r;
	if (x.shift < y.shift)
		v = x.shift,
		rx = bdd_and_ex(bx.h, y, ex, memo, m2, last),
		ry = bdd_and_ex(bx.l, y, ex, memo, m2, last);
	else if (x.shift > y.shift)
		v = y.shift,
		rx = bdd_and_ex(x, by.h, ex, memo, m2, last),
		ry = bdd_and_ex(x, by.l, ex, memo, m2, last);
	else
		v = x.shift,
		rx = bdd_and_ex(bx.h, by.h, ex, memo, m2, last),
		ry = bdd_and_ex(bx.l, by.l, ex, memo, m2, last);
	DBG(assert((size_t)v - 1 < ex.size());)
	r = ex[v - 1] ? bdd_or(rx, ry) : add(v, rx, ry);
	return memo.emplace(m, r), r;
}

struct sbdd_and_ex_perm {
	const bools& ex;
	const uints& p;
	unordered_map<array<bdd_ref, 2>, bdd_ref>& memo;
	unordered_map<bdd_ref, bdd_ref>& m2;
	int_t last;

	sbdd_and_ex_perm(const bools& ex, const uints& p,
	unordered_map<array<bdd_ref, 2>, bdd_ref>& memo,
	unordered_map<bdd_ref, bdd_ref>& m2) :
		ex(ex), p(p), memo(memo), m2(m2), last(0) {
			for (size_t n = 0; n != ex.size(); ++n)
				if (ex[n] || (p[n] != n)) last = n;
		}

	bdd_ref operator()(bdd_ref x, bdd_ref y) {
		DBG(assert(x.bdd_id && y.bdd_id);)
		if (x == F || y == F || x == -y) return F;
		if (x == T || x == y)
			return bdd::bdd_permute_ex(y, ex, p, last, m2);
		if (y == T) return bdd::bdd_permute_ex(x, ex, p, last, m2);
		if (x > y) swap(x, y);
		array<bdd_ref, 2> m = {x, y};
		auto it = memo.find(m);
		if (it != memo.end()) return it->second;
		const bdd bx = bdd::get(x), by = bdd::get(y);
		int_t v;
		bdd_ref rx, ry, r;
		if (x.shift > last+1 && y.shift > last+1)
			return memo.emplace(m, r = bdd::bdd_and(x, y)), r;
		if (x.shift < y.shift)
			v = x.shift, rx = (*this)(bx.h, y), ry = (*this)(bx.l, y);
		else if (x.shift > y.shift)
			v = y.shift, rx = (*this)(x, by.h), ry = (*this)(x, by.l);
		else v = x.shift, rx = (*this)(bx.h,by.h), ry = (*this)(bx.l,by.l);
		DBG(assert((size_t)v - 1 < ex.size());)
		r = ex[v - 1] ? bdd::bdd_or(rx, ry) :
			bdd::bdd_ite_var(p[v-1], rx, ry);
		return memo.emplace(m, r), r;
	}
};

bdd_ref bdd::bdd_and_ex(const bdd_ref &x, const bdd_ref & y, const bools& ex) {
	int_t last = 0;
	for (size_t n = 0; n != ex.size(); ++n) if (ex[n]) last = n;
	bdd_ref r = bdd_and_ex(x, y, ex, CX[ex], memos_ex[ex], last);
	DBG(bdd_ref t = bdd_ex(bdd_and(x, y), ex);)
	DBG(assert(r == t);)
	return r;
}

bdd_ref bdd::bdd_and_ex_perm(const bdd_ref &x, const bdd_ref & y, const bools& ex, const uints& p) {
	return sbdd_and_ex_perm(ex,p,CXP[{ex,p}],memos_perm_ex[{p,ex}])(x,y);
}

char bdd::bdd_and_many_ex_iter(const bdds& v, bdds& h, bdds& l, int_t& m) {
	size_t i, sh = 0, sl = 0;
	bdd_ref *b = (bdd_ref*)alloca(sizeof(bdd_ref) * v.size());
	for (i = 0; i != v.size(); ++i) b[i] = v[i];
	m = b[0].shift;//var(v[0]);
	for (i = 1; i != v.size(); ++i) m = min(m, (int_t) b[i].shift);//var(v[i]));
	bdd_ref *ph = (bdd_ref*)alloca(sizeof(bdd_ref) * v.size()),
		  *pl = (bdd_ref*)alloca(sizeof(bdd_ref) * v.size());
	for (i = 0; ph && i != v.size(); ++i)
		if (b[i].shift != m) ph[sh++] = v[i];
		else if (hi(b[i]) == F) ph = 0;
		else if (hi(b[i]) != T) ph[sh++] = hi(b[i]);
	for (i = 0; pl && i != v.size(); ++i)
		if (b[i].shift != m) pl[sl++] = v[i];
		else if (lo(b[i]) == F) pl = 0;
		else if (lo(b[i]) != T) pl[sl++] = lo(b[i]);
	if (ph) {
		h.resize(sh);
		while (sh--) h[sh] = ph[sh];
		am_sort(h);
	}
	if (pl) {
		l.resize(sl);
		while (sl--) l[sl] = pl[sl];
		am_sort(l);
		return ph ? 0 : 2;
	}
	return ph ? 1 : 3;
}

struct sbdd_and_many_ex {
	const bools& ex;
	unordered_map<bdds, bdd_ref>& memo;
	unordered_map<bdd_ref, bdd_ref>& m2;
	unordered_map<array<bdd_ref, 2>, bdd_ref>& m3;
	int_t last;

	sbdd_and_many_ex(const bools& ex, unordered_map<bdds, bdd_ref>& memo,
		unordered_map<bdd_ref, bdd_ref>& m2,
		unordered_map<array<bdd_ref, 2>, bdd_ref>& m3) :
		ex(ex), memo(memo), m2(m2), m3(m3), last(0) {
		for (size_t n = 0; n != ex.size(); ++n) if (ex[n]) last = n;
	}

	bdd_ref operator()(bdds v) {
		if (v.empty()) return T;
		if (v.size() == 1) return bdd::bdd_ex(v[0], ex, m2, last);
		if (v.size() == 2)
			return bdd::bdd_and_ex(v[0], v[1], ex, m3, m2, last);
		auto it = memo.find(v);
		if (it != memo.end()) return it->second;
		int_t m = 0;
		bdd_ref res = F, h, l;
		bdds vh, vl;
		char c = bdd::bdd_and_many_ex_iter(v, vh, vl, m);
		if (m > last+1) {
			switch (c) {
			case 0: res = bdd::add(m, bdd::bdd_and_many(move(vh)),
				bdd::bdd_and_many(move(vl))); break;
			case 1: res = bdd::add(m,bdd::bdd_and_many(move(vh)),F);
				break;
			case 2: res = bdd::add(m,F,bdd::bdd_and_many(move(vl)));
				break;
			case 3: res = F; break;
			default: DBGFAIL;
			}
		} else {
			switch (c) {
			case 0: l = (*this)(move(vl)), h = (*this)(move(vh));
				if (ex[m - 1]) res = bdd::bdd_or(h, l);
				else res = bdd::add(m, h, l);
				break;
			case 1: if (ex[m - 1]) res = (*this)(move(vh));
				else res = bdd::add(m, (*this)(move(vh)), F);
				break;
			case 2: if (ex[m - 1]) res = (*this)(move(vl));
				else res = bdd::add(m, F, (*this)(move(vl)));
				break;
			case 3: res = F; break;
			default: DBGFAIL;
			}
		}
		return memo.emplace(move(v), res).first->second;
	}
};

struct sbdd_and_many_ex_perm {
	const bools& ex;
	const uints& p;
	unordered_map<bdds, bdd_ref>& memo;
	//map<bdds, int_t, veccmp<int_t>>& memo;
	unordered_map<array<bdd_ref, 2>, bdd_ref>& m2;
	unordered_map<bdd_ref, bdd_ref>& m3;
	int_t last;
	sbdd_and_ex_perm saep;

	sbdd_and_many_ex_perm(const bools& ex, const uints& p,
		unordered_map<bdds, bdd_ref>& memo,
		unordered_map<array<bdd_ref, 2>, bdd_ref>& m2,
		unordered_map<bdd_ref, bdd_ref>& m3) :
		ex(ex), p(p), memo(memo), m2(m2), m3(m3), last(0),
		saep(ex, p, m2, m3) {
			for (size_t n = 0; n != ex.size(); ++n)
				if (ex[n] || (p[n] != n)) last = n;
		}

	bdd_ref operator()(bdds v) {
		if (v.empty()) return T;
		if (v.size() == 1)
			return bdd::bdd_permute_ex(v[0], ex, p, last, m3);
		if (v.size() == 2) return saep(v[0], v[1]);
		auto it = memo.find(v);
		if (it != memo.end()) return it->second;
		int_t m = 0;
		bdd_ref res = F, h, l;
		bdds vh, vl;
		char c = bdd::bdd_and_many_ex_iter(v, vh, vl, m);
		if (m > last+1) {
			switch (c) {
			case 0: res = bdd::add(m, bdd::bdd_and_many(move(vh)),
					bdd::bdd_and_many(move(vl))); break;
			case 1: res = bdd::add(m,bdd::bdd_and_many(move(vh)),F);
				break;
			case 2: res = bdd::add(m,F,bdd::bdd_and_many(move(vl)));
				break;
			case 3: res = F; break;
			default: DBGFAIL;
			}
		} else {
			switch (c) {
			case 0: l = (*this)(move(vl)), h = (*this)(move(vh));
				if (ex[m - 1]) res = bdd::bdd_or(h, l);
				else res = bdd::bdd_ite_var(p[m-1],h,l);
				break;
			case 1: if (ex[m - 1]) res = (*this)(move(vh));
				else res = bdd::bdd_ite_var(p[m-1],
					(*this)(move(vh)), F);
				break;
			case 2: if (ex[m - 1]) res = (*this)(move(vl));
				else res = bdd::bdd_ite_var(p[m-1], F,
					(*this)(move(vl)));
				break;
			case 3: res = F; break;
			default: DBGFAIL;
			}
		}
		return memo.emplace(move(v), res), res;
	}
};

bdd_ref bdd::bdd_and_many_ex(bdds v, const bools& ex) {
	bdd_ref r;
	DBG(bdd_ref t = bdd_ex(bdd_and_many(v), ex);)
	r = sbdd_and_many_ex(ex, AMX[ex], memos_ex[ex], CX[ex])(v);
	DBG(assert(r == t);)
	return r;
}

bdd_ref bdd::bdd_and_many_ex_perm(bdds v, const bools& ex, const uints& p) {
	return sbdd_and_many_ex_perm(ex, p, AMXP[{ex,p}], CXP[{ex,p}],
			memos_perm_ex[{p,ex}])(v);
}

void bdd::mark_all(const bdd_ref & i) {
	DBG(assert((size_t)i.bdd_id < V.size());)
	if (i.bdd_id >= 2 && !has(S, i.bdd_id))
		mark_all(hi(i)), mark_all(lo(i)), S.insert(i.bdd_id);
}

template <typename T>
basic_ostream<T>& bdd::stats(basic_ostream<T>& os) {
	return os << "S: " << S.size() << " V: "<< V.size() <<
		" AM: " << AM.size() << " C: "<< C.size();
}
template basic_ostream<char>& bdd::stats(basic_ostream<char>&);
template basic_ostream<wchar_t>& bdd::stats(basic_ostream<wchar_t>&);

void bdd::gc() {
	if(!gc_enabled) return;
	if (V.empty()) return;
	S.clear();
	for (auto x : bdd_handle::M) mark_all(x.first);
//	if (V.size() < S.size() << 3) return;
	Ma.clear(), S.insert(0), S.insert(1);
//	if (S.size() >= 1e+6) { o::err() << "out of memory" << endl; exit(1); }
	vector<int_t> p(V.size(), 0);
#ifndef NOMMAP
	bdd_mmap v1(memory_map_allocator<bdd>("", bdd_mmap_mode));
	v1.reserve(bdd_mmap_mode == MMAP_NONE ? S.size() : max_bdd_nodes);
#else
	bdd_mmap v1;
	v1.reserve(S.size());
#endif
	for (size_t n = 0; n < V.size(); ++n)
		if (has(S, n)) p[n] = v1.size(), v1.emplace_back(move(V[n]));
	OUT(stats(o::dbg())<<endl;)
	V = move(v1);
#define f(i) ((i.bdd_id = (p[i.bdd_id] ? p[i.bdd_id] : i.bdd_id)), i)
	for (size_t n = 2; n < V.size(); ++n) {
		DBG(assert(p[V[n].h.bdd_id] && p[V[n].l.bdd_id]);)
		f(V[n].h), f(V[n].l);
	}
	unordered_map<ite_memo, bdd_ref> c;
	unordered_map<bdds, bdd_ref> am;
	for (pair<ite_memo, bdd_ref> x : C)
		if (	has(S, x.first.x.bdd_id) &&
			has(S, x.first.y.bdd_id) &&
			has(S, x.first.z.bdd_id) &&
			has(S, x.second.bdd_id))
			f(x.first.x), f(x.first.y), f(x.first.z),
			x.first.rehash(), c.emplace(x.first, f(x.second));
	C = move(c);
	map<bools, unordered_map<array<bdd_ref, 2>, bdd_ref>, veccmp<bool>> cx;
	unordered_map<array<bdd_ref, 2>, bdd_ref> cc;
	for (const auto& x : CX) {
		for (pair<array<bdd_ref, 2>, bdd_ref> y : x.second)
			if (	has(S, y.first[0].bdd_id) &&
				has(S, y.first[1].bdd_id) &&
				has(S, y.second.bdd_id))
				f(y.first[0]), f(y.first[1]),
				cc.emplace(y.first, f(y.second));
		if (!cc.empty()) cx.emplace(x.first, move(cc));
	}
	CX = move(cx);
	map<pair<bools, uints>, unordered_map<array<bdd_ref, 2>, bdd_ref>,
		vec2cmp<bool, uint_t>> cxp;
	for (const auto& x : CXP) {
		for (pair<array<bdd_ref, 2>, bdd_ref> y : x.second)
			if (	has(S, y.first[0].bdd_id) &&
				has(S, y.first[1].bdd_id) &&
				has(S, y.second.bdd_id))
				f(y.first[0]), f(y.first[1]),
				cc.emplace(y.first, f(y.second));
		if (!cc.empty()) cxp.emplace(x.first, move(cc));
	}
	CXP = move(cxp);
	unordered_map<bdd_ref, bdd_ref> q;
	map<bools, unordered_map<bdd_ref, bdd_ref>, veccmp<bool>> mex;
	for (const auto& x : memos_ex) {
		for (pair<bdd_ref, bdd_ref> y : x.second)
			if (has(S, y.first.bdd_id) && has(S, y.second.bdd_id))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mex.emplace(x.first, move(q));
	}
	memos_ex = move(mex);
	map<uints, unordered_map<bdd_ref, bdd_ref>, veccmp<uint_t>> mp;
	for (const auto& x : memos_perm) {
		for (pair<bdd_ref, bdd_ref> y : x.second)
			if (has(S, y.first.bdd_id) && has(S, y.second.bdd_id))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mp.emplace(x.first, move(q));
	}
	memos_perm = move(mp);
	map<pair<uints, bools>, unordered_map<bdd_ref, bdd_ref>,
		vec2cmp<uint_t, bool>> mpe;
	for (const auto& x : memos_perm_ex) {
		for (pair<bdd_ref, bdd_ref> y : x.second)
			if (has(S, y.first.bdd_id) && has(S, y.second.bdd_id))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mpe.emplace(x.first, move(q));
	}
	memos_perm_ex = move(mpe);
	bool b;
	map<bools, unordered_map<bdds, bdd_ref>, veccmp<bool>> amx;
	for (const auto& x : AMX) {
		for (pair<bdds, bdd_ref> y : x.second) {
			b = false;
			for (bdd_ref& i : y.first)
				if ((b |= !has(S, i.bdd_id))) break;
				else f(i);
			if (!b && has(S, y.second.bdd_id))
				am.emplace(y.first, f(y.second));
		}
		if (!am.empty()) amx.emplace(x.first, move(am));
	}
	AMX = move(amx);
	map<pair<bools, uints>, unordered_map<bdds, bdd_ref>,
		vec2cmp<bool, uint_t>> amxp;
	for (const auto& x : AMXP) {
		for (pair<bdds, bdd_ref> y : x.second) {
			b = false;
			for (bdd_ref& i : y.first)
				if ((b |= !has(S, i.bdd_id))) break;
				else f(i);
			if (!b && has(S, y.second.bdd_id))
				am.emplace(y.first, f(y.second));
		}
		if (!am.empty()) amxp.emplace(x.first, move(am));
	}
	AMXP = move(amxp);
	for (pair<bdds, bdd_ref> x : AM) {
		b = false;
		for (bdd_ref& i : x.first)
			if ((b |= !has(S, i.bdd_id))) break;
			else f(i);
		if (!b&&has(S,x.second.bdd_id)) am.emplace(x.first, f(x.second));
	}
	AM=move(am), bdd_handle::update(p);
	p.clear(), S.clear();
	std::hash<bdd_ref> hsh;
	for (size_t n = 0; n < V.size(); ++n)
		Ma.emplace(bdd_key(hash_upair(hsh(V[n].h), hsh(V[n].l)),
			V[n].h, V[n].l), n);
	OUT(o::dbg() <<"AM: " << AM.size() << " C: "<< C.size() << endl;)
}

void bdd_handle::update(const vector<int_t>& p) {
	unordered_map<bdd_ref, weak_ptr<bdd_handle>> m;
	for (pair<bdd_ref, weak_ptr<bdd_handle>> x : M)
		//DBG(assert(!x.second.expired());) // is this needed? cannot load from archive with this
		if (!x.second.expired())
			f(x.second.lock()->b), m.emplace(f(x.first), x.second);
	M = move(m);
}
#undef f

spbdd_handle bdd_handle::get(const bdd_ref & b) {
	DBG(assert((size_t)b.bdd_id < V.size());)
	auto it = M.find(b);
	if (it != M.end()) return it->second.lock();
	spbdd_handle h(new bdd_handle(b));
	return M.emplace(b, weak_ptr<bdd_handle>(h)), h;
}

void bdd::bdd_sz(const bdd_ref &x, set<bdd_ref>& s) {
	if (!s.emplace(x).second) return;
	bdd_sz(hi(x), s), bdd_sz(lo(x), s);
}

spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y) {
	spbdd_handle r = bdd_handle::get(bdd::bdd_and(x->b, y->b));
	return r;
}

spbdd_handle operator%(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_and(x->b, -y->b));
}

spbdd_handle operator||(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_or(x->b, y->b));
}

spbdd_handle bdd_impl(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_or(-x->b, y->b));
}

bool bdd_subsumes(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd::bdd_subsumes(x->b, y->b);
}

spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y, cr_spbdd_handle z) {
	return bdd_handle::get(bdd::bdd_ite(x->b, y->b, z->b));
}

spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y, cr_spbdd_handle z) {
	return bdd_handle::get(bdd::bdd_ite_var(x, y->b, z->b));
}

spbdd_handle bdd_and_many(bdd_handles v) {
	if (V.size() >= gclimit) bdd::gc();
/*	if (v.size() > 16) {
		bdd_handles x, y;
		spbdd_handle r;
		for (size_t n = 0; n != v.size(); ++n)
			(n < v.size()>>1 ? x : y).push_back(v[n]);
		v.clear();
		r = bdd_and_many(move(x));
		return r && bdd_and_many(move(y));
	}*/
	bdds b;
	b.reserve(v.size());
	for (size_t n = 0; n != v.size(); ++n) b.push_back(v[n]->b);
	am_sort(b);
//	DBG( o::out()<<"am begin"<<endl;
	auto r = bdd_handle::get(bdd::bdd_and_many(move(b)));
//	DBG( o::out()<<"am end"<<endl;
	return r;
}

spbdd_handle bdd_and_many_ex(bdd_handles v, const bools& ex) {
	if (V.size() >= gclimit) bdd::gc();
	bool t = false;
	for (bool x : ex) t |= x;
	if (!t) return bdd_and_many(move(v));
	bdds b;
	b.reserve(v.size());
	for (size_t n = 0; n != v.size(); ++n) b.push_back(v[n]->b);
	am_sort(b);
	auto r = bdd_handle::get(bdd::bdd_and_many_ex(move(b), ex));
	return r;
}

spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const bools& ex,
	const uints& p) {
	if (V.size() >= gclimit) bdd::gc();
//	DBG(assert(bdd_nvars(v) < ex.size());)
//	DBG(assert(bdd_nvars(v) < p.size());)
	bdds b;
	b.reserve(v.size());
	for (size_t n = 0; n != v.size(); ++n) b.push_back(v[n]->b);
	am_sort(b);
	auto r = bdd_handle::get(bdd::bdd_and_many_ex_perm(move(b), ex, p));
	return r;
}

bdd_ref bdd_or_reduce(bdds b) {
	if (b.empty()) return F;
	if (b.size() == 1) return b[0];
	if (b.size() == 2) return bdd::bdd_or(b[0], b[1]);
	bdd_ref t = F;
	if (b.size() & 1) t = b.back(), b.erase(b.begin()+b.size()-1);
	bdds x(b.size()>>1);
	for (size_t n = 0; n != x.size(); ++n)
		x[n] = bdd::bdd_or(b[n<<1], b[1+(n<<1)]);
	return bdd::bdd_or(t, bdd_or_reduce(move(x)));
}

spbdd_handle bdd_or_many(bdd_handles v) {
	bdds b(v.size());
	for (size_t n = 0; n != v.size(); ++n) b[n] = v[n]->b;
	return bdd_handle::get(bdd_or_reduce(move(b)));
/*	int_t r = F;
	for (auto x : v) r = bdd::bdd_or(r, x->b);
	return bdd_handle::get(r);
	bdds b(v.size());
	for (size_t n = 0; n != v.size(); ++n) b[n] = -v[n]->b;
	return bdd_handle::get(-bdd::bdd_and_many(move(b)));*/
}

#define SATCOUNT
#ifdef SATCOUNT

size_t bdd::satcount_perm(const bdd_ref & x, size_t leafvar) {
	size_t r = 0;
	if (leaf(x)) return trueleaf(x) ? 1 : 0;
	const bdd bx = get(x);
	int_t hivar = leaf(bx.h) ? leafvar : bx.h.shift;
	int_t lovar = leaf(bx.l) ? leafvar : bx.l.shift;
	r += satcount_perm(bx.h, leafvar) *
		(1 << (hivar - x.shift - 1));
	r += satcount_perm(bx.l, leafvar) *
		(1 << (lovar - x.shift - 1));
	return r;
}

static set<size_t> ourvars;
size_t bdd::getvar(const bdd_ref &h, const bdd_ref &l, int_t v, const bdd_ref & x, size_t maxv) {
	if (leaf(x)) return maxv;
	const bdd bhi = get(h), blo = get(l);
	maxv = leaf(h) ? maxv : max(maxv, getvar(bhi.h, bhi.l, h.shift, h, maxv));
	maxv = leaf(l) ? maxv : max(maxv, getvar(blo.h, blo.l, l.shift, l, maxv));
	maxv = max(maxv, size_t(v));
	ourvars.insert(v);
	return maxv;
}

// D: this version does a manual 'permute' (in place alligns vars)
// works better with rule(?x ?y ?out) :- headers
// could be buggy (when bdd is minimized, vars removed, we're only guessing)
size_t bdd::satcount_k(const bdd_ref & x, const bools& ex, const uints&) {
	const bdd bx = get(x);
	ourvars.clear();
	size_t leafvar = getvar(bx.h, bx.l, x.shift, x, 0) + 1;

	// this's what's missing, if size is smaller means we don't have the 0-var,
	// but this might be correct or not, we might be missing one in the middle?
	size_t k = 1;
	size_t n = count_if(ex.begin(), ex.end(), [](bool isex) { return !isex; });
	if (ourvars.size() < n)
		k = 1 << (n - ourvars.size());

	map<int_t, int_t> inv;
	int_t ivar = 1;
	for (auto x : ourvars) {
		//o::dbg() << "satcount: inv: " << x << ", " << ivar << " ." << endl;
		inv.emplace(x, ivar++);
	}
	leafvar = ivar;

	return k * satcount_k(x, leafvar, inv);
}

size_t bdd::satcount_k(const bdd_ref &x, size_t leafvar,
	map<int_t, int_t>& mapvars) {
	size_t r = 0;
	if (leaf(x)) {
		return trueleaf(x) ? 1 : 0;
	}
	const bdd bx = get(x);
	int_t hivar = leaf(bx.h) ? leafvar : mapvars.at(bx.h.shift); // nvars + 1 - x.shift
	int_t lovar = leaf(bx.l) ? leafvar : mapvars.at(bx.l.shift);
	r += satcount_k(bx.h, leafvar, mapvars) *
		(1 << (hivar - mapvars.at(x.shift) - 1));
	r += satcount_k(bx.l, leafvar, mapvars) *
		(1 << (lovar - mapvars.at(x.shift) - 1));
	return r;
}

size_t bdd::satcount(spbdd_handle x, const bools& inv) {
	// see: body::init_perm_inv(args)
	// only count alt vars that are 'possible permutes' (of a body bit) 
	// all other var/const bits are inconsequential for this count
	// (so we 'zero' them all to always be the same)
	// i.e. these are bits possibly 'affected' by this body's bdd
	// TODO: is it still possible that
	// a) those bits are affected by something else, not body's bdd?
	// b) other (unlisted) bits are affected via some bdd conversion?

	return satcount_iter(x, inv.size(), inv).count();
}

void satcount_iter::sat(const bdd_ref & x) {
	if (x == F) return;
	const bdd bx = bdd::get(x);
	if (!bdd::leaf(x) && v < bdd::var(x)) {
		DBG(assert(bdd::var(x) <= nvars);)
			p[++v - 2] = true, sat(x), p[v - 2] = false, sat(x), --v;
	}
	else if (v != nvars + 1)
		p[++v - 2] = true, sat(bx.h),
		p[v - 2] = false, sat(bx.l), --v;
	else { 
		//f(p, x); 
		DBG(assert(x.abs() == T););
		bools np(p.size());
		for (size_t i = 0; i < p.size(); ++i)
			np[i] = !inv[i] ? true : p[i];
		vp.insert(np);
	}
}

#endif

void bdd::sat(uint_t v, uint_t nvars, const bdd_ref & t, bools& p, vbools& r) {
	if (t == F) return;
	if (!leaf(t) && v < var(t))
		p[v - 1] = true, sat(v + 1, nvars, t, p, r),
		p[v - 1] = false, sat(v + 1, nvars, t, p, r);
	else if (v != nvars) {
		p[v - 1] = true, sat(v + 1, nvars, hi(t), p, r),
		p[v - 1] = false, sat(v + 1, nvars, lo(t), p, r);
	} else	r.push_back(p);
}

vbools bdd::allsat(const bdd_ref & x, uint_t nvars) {
	bools p(nvars);
	vbools r;
	return sat(1, nvars + 1, x, p, r), r;
}

vbools allsat(cr_spbdd_handle x, uint_t nvars) {
	return bdd::allsat(x->b, nvars);
}

void allsat_cb::sat(const bdd_ref & x) {
	if (x == F) return;
	const bdd bx = bdd::get(x);
	if (!bdd::leaf(x) && v < bdd::var(x)) {
		DBG(assert(bdd::var(x) <= nvars);)
		p[++v-2] = true, sat(x), p[v-2] = false, sat(x), --v;
	} else if (v != nvars + 1)
		p[++v-2] = true, sat(bx.h),
		p[v-2] = false, sat(bx.l), --v;
	else f(p, x);
}

bdd_ref bdd::bdd_xor(const bdd_ref &x, const bdd_ref & y) { return bdd_ite(x,-y,y); }

spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_xor(x->b,y->b));
}

bdd_ref bdd::bdd_ex(const bdd_ref &x, const bools& b, unordered_map<bdd_ref, bdd_ref>& memo,
	int_t last) {
	if (leaf(x) || (int_t)var(x) > last+1) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	DBG(assert(var(x)-1 < b.size());)
	if (b[var(x) - 1]) return bdd_ex(bdd_or(hi(x), lo(x)), b, memo, last);
	return memo.emplace(x, bdd::add(var(x), bdd_ex(hi(x), b, memo, last),
				bdd_ex(lo(x), b, memo, last))).first->second;
}

bdd_ref bdd::bdd_ex(const bdd_ref & x, const bools& b) {
	int_t last = 0;
	for (size_t n = 0; n != b.size(); ++n) if (b[n]) last = n;
	return bdd_ex(x, b, memos_ex[b], last);
}

spbdd_handle operator/(cr_spbdd_handle x, const bools& b) {
	return bdd_handle::get(bdd::bdd_ex(x->b, b));
}

bdd_ref bdd::bdd_permute(const bdd_ref& x, const uints& m,
		unordered_map<bdd_ref, bdd_ref>& memo) {
	if (leaf(x) || m.size() <= var(x)-1) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	return memo.emplace(x, bdd_ite_var(m[var(x)-1],
		bdd_permute(hi(x), m, memo),
		bdd_permute(lo(x), m, memo))).first->second;
}

spbdd_handle operator^(cr_spbdd_handle x, const uints& m) {
//	DBG(assert(bdd_nvars(x) < m.size());)
	return bdd_handle::get(bdd::bdd_permute(x->b, m, memos_perm[m]));
}

bdd_ref bdd::bdd_permute_ex(const bdd_ref &x, const bools& b, const uints& m, size_t last,
	unordered_map<bdd_ref, bdd_ref>& memo) {
	if (leaf(x) || var(x) > last+1) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	bdd_ref t = x, y = x;
	DBG(assert(b.size() >= var(x));)
	for (bdd_ref r; var(y)-1 < b.size() && b[var(y)-1]; y = r)
		if (leaf((r = bdd_or(hi(y), lo(y)))))
			return memo.emplace(t, r), r;
		DBG(else assert(b.size() >= var(r));)
	DBG(assert(!leaf(y) && m.size() >= var(y));)
	return	memo.emplace(t, bdd_ite_var(m[var(y)-1],
		bdd_permute_ex(hi(y), b, m, last, memo),
		bdd_permute_ex(lo(y), b, m, last, memo))).first->second;
}

bdd_ref bdd::bdd_permute_ex(const bdd_ref & x, const bools& b, const uints& m) {
	size_t last = 0;
	for (size_t n = 0; n != b.size(); ++n) if (b[n] || (m[n]!=n)) last = n;
	return bdd_permute_ex(x, b, m, last, memos_perm_ex[{m,b}]);
}

spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const uints& m) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(x) < m.size());)
	return bdd_handle::get(bdd::bdd_permute_ex(x->b, b, m));
}

spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(x) < m.size());)
//	DBG(assert(bdd_nvars(y) < b.size());)
//	DBG(assert(bdd_nvars(y) < m.size());)
	return bdd_handle::get(bdd::bdd_and_ex_perm(x->b, y->b, b, m));
}

spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(y) < b.size());)
//	out(o::out(), x)<<endl<<endl;
//	out(o::out(), y)<<endl<<endl;
	return bdd_handle::get(bdd::bdd_and_ex(x->b, y->b, b));
}

spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(y) < b.size());)
	return bdd_handle::get(bdd::bdd_and_ex(x->b, -y->b, b));
}

spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(y) < b.size());)
//	DBG(assert(bdd_nvars(x) < m.size());)
//	DBG(assert(bdd_nvars(y) < m.size());)
	return bdd_handle::get(bdd::bdd_and_ex_perm(x->b, -y->b, b, m));
}

spbdd_handle from_bit(uint_t b, bool v) {
	return bdd_handle::get(bdd::from_bit(b, v));
}

spbdd_handle from_eq(uint_t x, uint_t y) {
	return bdd_ite(from_bit(x,true), from_bit(y,true), from_bit(y,false));
}

bool bdd::solve(const bdd_ref &x, int_t v, bdd_ref& l, bdd_ref &h) {
	bools b(v, false);
	b[v-1] = true;
	bdd_ref r = bdd_or( l = bdd_and_ex(x, from_bit(v, true), b),
			-(h = -bdd_and_ex(x, from_bit(v, true), b)));
	return leaf(r) && !trueleaf(r);
}

array<spbdd_handle, 2> solve(spbdd_handle x, int_t v) {
	bdd_ref h, l;
	if (!bdd::solve(x->b, v, h, l)) return { nullptr, nullptr };
	return { bdd_handle::get(l), bdd_handle::get(h) };
}

void bdd::bdd_nvars(const bdd_ref & x, set<int_t>& s) {
	if (!leaf(x)) s.insert(var(x)-1), bdd_nvars(hi(x),s),bdd_nvars(lo(x),s);
}

size_t bdd::bdd_nvars(const bdd_ref & x) {
	if (leaf(x)) return 0;
	set<int_t> s;
	bdd_nvars(x, s);
	size_t r = *s.rbegin();
	return r;
}

size_t bdd_nvars(bdd_handles x) {
	size_t r = 0;
	for (auto y : x) r = max(r, bdd_nvars(y));
	return r;
}

size_t bdd_nvars(spbdd_handle x) { return bdd::bdd_nvars(x->b); }
bool leaf(cr_spbdd_handle h) { return bdd::leaf(h->b); }
bool trueleaf(cr_spbdd_handle h) { return bdd::trueleaf(h->b); }
template <typename T>
basic_ostream<T>& out(basic_ostream<T>& os, cr_spbdd_handle x) { return bdd::out(os, x->b); }
template basic_ostream<char>& out(basic_ostream<char>&, cr_spbdd_handle);
template basic_ostream<wchar_t>& out(basic_ostream<wchar_t>&, cr_spbdd_handle);


size_t hash<ite_memo>::operator()(const ite_memo& m) const {
	return m.hash;
}

size_t hash<array<int_t, 2>>::operator()(const array<int_t, 2>& x) const {
	return hash_pair(x[0], x[1]);
}

size_t hash<array<bdd_ref, 2>>::operator()(const array<bdd_ref, 2>& x) const {
	std::hash<bdd_ref> hsh;
	return hash_upair(hsh(x[0]), hsh(x[1]));
}

size_t hash<bdd_key>::operator()(const bdd_key& k) const {return k.hash;}

bdd::bdd(const bdd_ref &h, const bdd_ref & l) : h(h), l(l) {
//	DBG(assert(V.size() < 2 || (v && h && l));)
}

template <typename T>
basic_ostream<T>& bdd::out(basic_ostream<T>& os, const bdd_ref & x) {
	if (leaf(x)) return os << (trueleaf(x) ? 'T' : 'F');
	//return out(out(os << b.v << " ? ", b.h) << " : ", b.l);
	return out(out(os << x.shift << " ? (", hi(x)) << ") : (", lo(x)) << ")";
}
