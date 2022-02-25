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

// Maps a BDD definition its unique ID
unordered_map<bdd_key, bdd_id> id_map;
// Maps a BDD ID to its (unique) definition
bdd_mmap V;
// Controls whether or not garbage collection is enabled
bool gc_enabled = true;
#ifndef NOMMAP
size_t max_bdd_nodes = 0;
mmap_mode bdd_mmap_mode = MMAP_NONE;
string bdd_mmap_file = "";
#endif
// Maps a BDD triple (a,b,c) to the BDD corresponding to (a&b)|(~a&c)
unordered_map<ite_memo, bdd_ref> C;
// Maps a BDD pair (a,b) and variable list c to the BDD exists c (a&b)
map<bools, unordered_map<array<bdd_ref, 2>, bdd_ref>, veccmp<bool>> CX;
// Maps a BDD pair (a,b), variable list c, and permutation list d to the BDD
// exists c (a&b) with its variables renamed according d
map<pair<bools, bdd_shfts>, unordered_map<array<bdd_ref, 2>, bdd_ref>,
	vec2cmp<bool, bdd_shft>> CXP;
// Maps a BDD vector a to the BDD corresponding to a_0 & a_1 & ... & a_N
unordered_map<bdds, bdd_ref> AM;
// Maps a BDD vector a and variable list b to the BDD exists b (a_0 & ... & a_N)
map<bools, unordered_map<bdds, bdd_ref>, veccmp<bool>> AMX;
// Maps a BDD vector a, variable list b, and permutation list c to the BDD
// exists b (a_0 & ... & a_N) with the variables renamed according c
map<pair<bools, bdd_shfts>, unordered_map<bdds, bdd_ref>, vec2cmp<bool, bdd_shft>> AMXP;
// Used to store the marked set in the mark-and-sweep garbage collector
unordered_set<bdd_id> S;
// Maps a live BDD to the handle that keeps it alive
unordered_map<bdd_ref, weak_ptr<bdd_handle>> bdd_handle::M;
spbdd_handle htrue, hfalse;
// Maps a BDD a and variable list b to the BDD corresponding to exists b (a)
map<bools, unordered_map<bdd_ref, bdd_ref>, veccmp<bool>> memos_ex;
// Maps a BDD a and permutation list b to the BDD a with the variables renamed
// according to b
map<bdd_shfts, unordered_map<bdd_ref, bdd_ref>, veccmp<bdd_shft>> memos_perm;
// Maps a BDD a, variable list b, and permutation list c to the BDD exists b (a)
// with the variables renamed according to c
map<pair<bdd_shfts, bools>, unordered_map<bdd_ref, bdd_ref>, vec2cmp<bdd_shft, bool>>
	memos_perm_ex;

_Pragma("GCC diagnostic push")
_Pragma("GCC diagnostic ignored \"-Wstrict-overflow\"")
auto am_cmp = [](bdd_ref x, bdd_ref y) {
	bool s = BDD_LT(x, y);
	x = BDD_ABS(x), y = BDD_ABS(y);
	return x < y ? true : x == y ? s : false;
};
_Pragma("GCC diagnostic pop")

size_t gclimit = 1e+7;

#ifndef NOMMAP
void bdd::init(mmap_mode m, size_t max_size, const string fn) {
	bdd_mmap_mode = m;
	if ((max_bdd_nodes = max_size / sizeof(bdd)) < 2) max_bdd_nodes = 2;
	V = bdd_mmap(memory_map_allocator<bdd>(fn, m));
	if (m != MMAP_NONE) V.reserve(max_bdd_nodes);
#else
void bdd::init() {
#endif
	//DBG(o::dbg() << "bdd::init(m: MMAP_" <<
	//	(m == MMAP_NONE ? "NONE" : "WRITE") <<
	//	", max_size: " << max_size << ", fn: " << fn
	//	<< ") max_bdd_nodes=" << max_bdd_nodes << "\n";)
	S.insert(0), S.insert(1), V.emplace_back(0, 0), // dummy
	V.emplace_back(1, 1),
	id_map.emplace(bdd_key(hash_pair(0, 0), 0, 0), 0),
	id_map.emplace(bdd_key(hash_pair(1, 1), 1, 1), 1),
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

/* Make a BDD reference representing a function f that behaves like the provided
 * high reference, h, if v is set to 1, otherwise it behaves like the provided
 * low reference, l. Precondition is that h and l depend only on variables after
 * v, i.e. their shifts are more than v. */

bdd_ref bdd::add(bdd_shft v, bdd_ref h, bdd_ref l) {
	DBG(assert(GET_BDD_ID(h) && GET_BDD_ID(l)););
	// If BDD would not branch on this variable, exclude it to preserve canonicity
	if (h == l) return h;
	// Apply output inversion invariant that low part can never be inverted
	const bool inv_out = GET_INV_OUT(l);
	// First apply the inverse shift since h and l will be attached to v
	h = inv_out ? FLIP_INV_OUT(MINUS_SHIFT(h, v)) : MINUS_SHIFT(h, v);
	l = inv_out ? FLIP_INV_OUT(MINUS_SHIFT(l, v)) : MINUS_SHIFT(l, v);
	// Now we know what v's child nodes will be, order them to maximize re-use
	// attaching an input inverter if necessary. Required for canonicity.
	const bool inv_inp = BDD_LT(l, h);
	if (inv_inp) swap(h, l);
	bdd_key k = bdd_key(hash_upair(h, l), h, l);
	unordered_map<bdd_key, bdd_id>::const_iterator it;
	// Find a BDD with the given high and low parts and make an attributed
	// reference to it.
	bdd_id id = (it = id_map.find(k)) != id_map.end() ? it->second :
		(V.emplace_back(h, l),
		id_map.emplace(move(k), V.size()-1),
		V.size()-1);
	return BDD_REF(id, v, inv_inp, inv_out);
}

bdd_ref bdd::from_bit(bdd_shft b, bool v) {
	return v ? add(b + 1, T, F) : add(b + 1, F, T);
}

bool bdd::bdd_subsumes(bdd_ref x, bdd_ref y) {
	if (x == T) return true;
	if (x == F) return y == F;
	if (y == T) return false;
	if (y == F) return true;
	const bdd bx = get(x), by = get(y);
	if (GET_SHIFT(x) < GET_SHIFT(y)) return bdd_subsumes(bx.h, y) && bdd_subsumes(bx.l, y);
	if (GET_SHIFT(x) > GET_SHIFT(y)) return bdd_subsumes(x, by.h) && bdd_subsumes(x, by.l);
	return bdd_subsumes(bx.h, by.h) && bdd_subsumes(bx.l, by.l);
}

/* Compute the conjunction of the given pair of BDDs. */

bdd_ref bdd::bdd_and(bdd_ref x, bdd_ref y) {
	DBG(assert(GET_BDD_ID(x) && GET_BDD_ID(y));)
	if (x == F || y == F || x == FLIP_INV_OUT(y)) return F;
	if (x == T || x == y) return y;
	if (y == T) return x;
	if (BDD_LT(y, x)) swap(x, y);
	// Downshift the input BDDs by their greatest common shift. Operate on this
	// reduced form then upshift the result by the aforementioned shift. Intent is
	// that this canonisation increases cache hits.
	const bdd_shft min_shift = min(GET_SHIFT(x), GET_SHIFT(y));
	DECR_SHIFT(x, min_shift);
	DECR_SHIFT(y, min_shift);
#ifdef MEMO
	ite_memo m = { x, y, F };
	auto it = C.find(m);
	// Upshift result to obtain answer for pre-downshifted BDDs
	if (it != C.end()) return PLUS_SHIFT(it->second, min_shift);
#endif
	const bdd_shft xshift = GET_SHIFT(x), yshift = GET_SHIFT(y);
	const bdd bx = get(x), by = get(y);
	bdd_ref r;
	if (xshift < yshift) r = add(xshift, bdd_and(bx.h, y), bdd_and(bx.l, y));
	else if (xshift > yshift) r = add(yshift, bdd_and(x, by.h), bdd_and(x, by.l));
	else r = add(xshift, bdd_and(bx.h, by.h), bdd_and(bx.l, by.l));
#ifdef MEMO
	if (C.size() < gclimit) C.emplace(m, r);
#endif
	// Upshift result to obtain answer for pre-downshifted BDDs
	return PLUS_SHIFT(r, min_shift);
}

bdd_ref bdd::bdd_ite_var(bdd_shft x, bdd_ref y, bdd_ref z) {
	if (x+1 < var(y) && x+1 < var(z)) return add(x+1, y, z);
	return bdd_ite(from_bit(x, true), y, z);
}

/* Compute x -> y, z from the given triple of BDDs. I.e. (x && y) || (~x && y). */

bdd_ref bdd::bdd_ite(bdd_ref x, bdd_ref y, bdd_ref  z) {
	DBG(assert(GET_BDD_ID(x) && GET_BDD_ID(y) && GET_BDD_ID(z));)
	if (GET_INV_OUT(x)) return bdd_ite(FLIP_INV_OUT(x), z, y);
	if (x == F) return z;
	if (x == T || y == z) return y;
	if (x == FLIP_INV_OUT(y) || x == z) return F;
	if (y == T) return bdd_or(x, z);
	if (y == F) return bdd_and(FLIP_INV_OUT(x), z);
	if (z == F) return bdd_and(x, y);
	if (z == T) return bdd_or(FLIP_INV_OUT(x), y);
	// Downshift the input BDDs by their greatest common shift. Operate on this
	// reduced form then upshift the result by the aforementioned shift. Intent is
	// that this canonisation increases cache hits.
	const bdd_shft min_shift = min(GET_SHIFT(x), min(GET_SHIFT(y), GET_SHIFT(z)));
	DECR_SHIFT(x, min_shift);
	DECR_SHIFT(y, min_shift);
	DECR_SHIFT(z, min_shift);
	auto it = C.find({x, y, z});
	// If result in cache then upshift to obtain answer for pre-downshifted BDDs
	if (it != C.end()) return PLUS_SHIFT(it->second, min_shift);
	bdd_ref r;
	const bdd bx = get(x), by = get(y), bz = get(z);
	const bdd_shft xshift = GET_SHIFT(x), yshift = GET_SHIFT(y), zshift = GET_SHIFT(z);
	if (xshift == yshift && yshift == zshift)
		r =	add(xshift, bdd_ite(bx.h, by.h, bz.h),
				bdd_ite(bx.l, by.l, bz.l));
	else if (!xshift && !yshift)
		r =	add(xshift, bdd_ite(bx.h, by.h, z),
				bdd_ite(bx.l, by.l, z));
	else if (!yshift && !zshift)
		r =	add(yshift, bdd_ite(x, by.h, bz.h),
				bdd_ite(x, by.l, bz.l));
	else if (!xshift && !zshift)
		r =	add(xshift, bdd_ite(bx.h, y, bz.h),
				bdd_ite(bx.l, y, bz.l));
	else if (!xshift)
		r =	add(xshift, bdd_ite(bx.h, y, z), bdd_ite(bx.l, y, z));
	else if (!yshift)
		r =	add(yshift, bdd_ite(x, by.h, z), bdd_ite(x, by.l, z));
	else	r =	add(zshift, bdd_ite(x, y, bz.h), bdd_ite(x, y, bz.l));
	// Upshift result to obtain answer for pre-downshifted BDDs
	if (C.size() > gclimit) return PLUS_SHIFT(r, min_shift);
	return C.emplace(ite_memo{x, y, z}, r), PLUS_SHIFT(r, min_shift);
}

void am_sort(bdds& b) {
	sort(b.begin(), b.end(), am_cmp);
	for (size_t n = 0; n < b.size();)
		if (b[n] == T) b.erase(b.begin() + n);
		else if (b[n] == F) { b = {F}; return; }
		else if (!n) { ++n; continue; }
		else if (b[n] == b[n-1]) b.erase(b.begin() + n);
		else if (b[n] == FLIP_INV_OUT(b[n-1])) { b = {F}; return; }
		else ++n;
}

size_t bdd::bdd_and_many_iter(bdds v, bdds& h, bdds& l, bdd_ref &res, bdd_shft &m){
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
		am_cmp(BDD_ABS(big[big.size()-1]), BDD_ABS(small[0])) ||
		am_cmp(BDD_ABS(small[small.size()-1]), BDD_ABS(big[0])))
		return false;
	for (bdd_ref t : small) if (!hasbc(big, t, am_cmp)) return false;
	return true;
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
	am_sort(v);
	if (v.empty()) return T;
	if (v.size() == 1) return v[0];
	auto it = AM.find(v);
	if (it != AM.end()) return it->second;
	if (v.size() == 2)
		return AM.emplace(v, bdd_and(v[0], v[1])).first->second;
	bdd_ref res = F, h, l;
	bdd_shft m = 0;
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
	unordered_map<bdd_ref, bdd_ref>& m2, bdd_shft last) {
	DBG(assert(GET_BDD_ID(x) && GET_BDD_ID(y));)
	if (x == F || y == F || x == FLIP_INV_OUT(y)) return F;
	if (x == T || x == y) return bdd_ex(y, ex, m2, last);
	if (y == T) return bdd_ex(x, ex, m2, last);
	if (x > y) swap(x, y);
	array<bdd_ref, 2> m = {x, y};
	auto it = memo.find(m);
	if (it != memo.end()) return it->second;
	const bdd bx = get(x), by = get(y);
	bdd_shft v;
	bdd_ref rx, ry, r;
	if (GET_SHIFT(x) > last+1 && GET_SHIFT(y) > last+1)
		return memo.emplace(m, r = bdd_and(x, y)), r;
	if (GET_SHIFT(x) < GET_SHIFT(y))
		v = GET_SHIFT(x),
		rx = bdd_and_ex(bx.h, y, ex, memo, m2, last),
		ry = bdd_and_ex(bx.l, y, ex, memo, m2, last);
	else if (GET_SHIFT(x) > GET_SHIFT(y))
		v = GET_SHIFT(y),
		rx = bdd_and_ex(x, by.h, ex, memo, m2, last),
		ry = bdd_and_ex(x, by.l, ex, memo, m2, last);
	else
		v = GET_SHIFT(x),
		rx = bdd_and_ex(bx.h, by.h, ex, memo, m2, last),
		ry = bdd_and_ex(bx.l, by.l, ex, memo, m2, last);
	DBG(assert((size_t)v - 1 < ex.size());)
	r = ex[v - 1] ? bdd_or(rx, ry) : add(v, rx, ry);
	return memo.emplace(m, r), r;
}

struct sbdd_and_ex_perm {
	const bools& ex;
	const bdd_shfts& p;
	unordered_map<array<bdd_ref, 2>, bdd_ref>& memo;
	unordered_map<bdd_ref, bdd_ref>& m2;
	bdd_shft last;

	sbdd_and_ex_perm(const bools& ex, const bdd_shfts& p,
	unordered_map<array<bdd_ref, 2>, bdd_ref>& memo,
	unordered_map<bdd_ref, bdd_ref>& m2) :
		ex(ex), p(p), memo(memo), m2(m2), last(0) {
			for (size_t n = 0; n != ex.size(); ++n)
				if (ex[n] || (p[n] != n)) last = n;
		}

	bdd_ref operator()(bdd_ref x, bdd_ref y) {
		DBG(assert(GET_BDD_ID(x) && GET_BDD_ID(y));)
		if (x == F || y == F || x == FLIP_INV_OUT(y)) return F;
		if (x == T || x == y)
			return bdd::bdd_permute_ex(y, ex, p, last, m2);
		if (y == T) return bdd::bdd_permute_ex(x, ex, p, last, m2);
		if (x > y) swap(x, y);
		array<bdd_ref, 2> m = {x, y};
		auto it = memo.find(m);
		if (it != memo.end()) return it->second;
		const bdd bx = bdd::get(x), by = bdd::get(y);
		bdd_shft v;
		bdd_ref rx, ry, r;
		if (GET_SHIFT(x) > last+1 && GET_SHIFT(y) > last+1)
			return memo.emplace(m, r = bdd::bdd_and(x, y)), r;
		if (GET_SHIFT(x) < GET_SHIFT(y))
			v = GET_SHIFT(x), rx = (*this)(bx.h, y), ry = (*this)(bx.l, y);
		else if (GET_SHIFT(x) > GET_SHIFT(y))
			v = GET_SHIFT(y), rx = (*this)(x, by.h), ry = (*this)(x, by.l);
		else v = GET_SHIFT(x), rx = (*this)(bx.h,by.h), ry = (*this)(bx.l,by.l);
		DBG(assert((size_t)v - 1 < ex.size());)
		r = ex[v - 1] ? bdd::bdd_or(rx, ry) :
			bdd::bdd_ite_var(p[v-1], rx, ry);
		return memo.emplace(m, r), r;
	}
};

bdd_ref bdd::bdd_and_ex(bdd_ref x, bdd_ref  y, const bools& ex) {
	bdd_shft last = 0;
	for (bdd_shft n = 0; n != ex.size(); ++n) if (ex[n]) last = n;
	bdd_ref r = bdd_and_ex(x, y, ex, CX[ex], memos_ex[ex], last);
	DBG(bdd_ref t = bdd_ex(bdd_and(x, y), ex);)
	DBG(assert(r == t);)
	return r;
}

bdd_ref bdd::bdd_and_ex_perm(bdd_ref x, bdd_ref  y, const bools& ex, const bdd_shfts& p) {
	return sbdd_and_ex_perm(ex,p,CXP[{ex,p}],memos_perm_ex[{p,ex}])(x,y);
}

char bdd::bdd_and_many_ex_iter(const bdds& v, bdds& h, bdds& l, bdd_shft& m) {
	size_t i, sh = 0, sl = 0;
	bdd *b = (bdd*)alloca(sizeof(bdd) * v.size());
	for (i = 0; i != v.size(); ++i) b[i] = get(v[i]);
	m = GET_SHIFT(v[0]);//var(v[0]);
	for (i = 1; i != v.size(); ++i) m = min(m, GET_SHIFT(v[i]));//var(v[i]));
	bdd_ref *ph = (bdd_ref*)alloca(sizeof(bdd_ref) * v.size()),
		  *pl = (bdd_ref*)alloca(sizeof(bdd_ref) * v.size());
	for (i = 0; ph && i != v.size(); ++i)
		if (GET_SHIFT(v[i]) != m) ph[sh++] = v[i];
		else if (b[i].h == F) ph = 0;
		else if (b[i].h != T) ph[sh++] = b[i].h;
	for (i = 0; pl && i != v.size(); ++i)
		if (GET_SHIFT(v[i]) != m) pl[sl++] = v[i];
		else if (b[i].l == F) pl = 0;
		else if (b[i].l != T) pl[sl++] = b[i].l;
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
	bdd_shft last;

	sbdd_and_many_ex(const bools& ex, unordered_map<bdds, bdd_ref>& memo,
		unordered_map<bdd_ref, bdd_ref>& m2,
		unordered_map<array<bdd_ref, 2>, bdd_ref>& m3) :
		ex(ex), memo(memo), m2(m2), m3(m3), last(0) {
		for (bdd_shft n = 0; n != ex.size(); ++n) if (ex[n]) last = n;
	}

	bdd_ref operator()(bdds v) {
		if (v.empty()) return T;
		if (v.size() == 1) return bdd::bdd_ex(v[0], ex, m2, last);
		if (v.size() == 2)
			return bdd::bdd_and_ex(v[0], v[1], ex, m3, m2, last);
		auto it = memo.find(v);
		if (it != memo.end()) return it->second;
		bdd_shft m = 0;
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
	const bdd_shfts& p;
	unordered_map<bdds, bdd_ref>& memo;
	//map<bdds, bdd_ref, veccmp<bdd_ref>>& memo;
	unordered_map<array<bdd_ref, 2>, bdd_ref>& m2;
	unordered_map<bdd_ref, bdd_ref>& m3;
	bdd_shft last;
	sbdd_and_ex_perm saep;

	sbdd_and_many_ex_perm(const bools& ex, const bdd_shfts& p,
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
		bdd_shft m = 0;
		bdd_ref res = F, h, l;
		bdds vh, vl;
		char c = bdd::bdd_and_many_iter(v, vh, vl, res, m);
		if (m > last+1) {
			switch (c) {
			case 0: res = bdd::add(m, bdd::bdd_and_many(move(vh)),
					bdd::bdd_and_many(move(vl))); break;
			case 2: res = bdd::add(m,bdd::bdd_and_many(move(vh)),F);
				break;
			case 3: res = bdd::add(m,F,bdd::bdd_and_many(move(vl)));
				break;
			case 1: res = F; break;
			default: DBGFAIL;
			}
		} else {
			switch (c) {
			case 0: l = (*this)(move(vl)), h = (*this)(move(vh));
				if (ex[m - 1]) res = bdd::bdd_or(h, l);
				else res = bdd::bdd_ite_var(p[m-1],h,l);
				break;
			case 2: if (ex[m - 1]) res = (*this)(move(vh));
				else res = bdd::bdd_ite_var(p[m-1],
					(*this)(move(vh)), F);
				break;
			case 3: if (ex[m - 1]) res = (*this)(move(vl));
				else res = bdd::bdd_ite_var(p[m-1], F,
					(*this)(move(vl)));
				break;
			case 1: res = F; break;
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

bdd_ref bdd::bdd_and_many_ex_perm(bdds v, const bools& ex, const bdd_shfts& p) {
	return sbdd_and_many_ex_perm(ex, p, AMXP[{ex,p}], CXP[{ex,p}],
			memos_perm_ex[{p,ex}])(v);
}

void bdd::mark_all(bdd_ref i) {
	DBG(assert((size_t)GET_BDD_ID(i) < V.size());)
	if (GET_BDD_ID(i) >= 2 && !has(S, GET_BDD_ID(i)))
		mark_all(hi(i)), mark_all(lo(i)), S.insert(GET_BDD_ID(i));
}

/* Get the size of the ITE cache. */
size_t bdd::get_ite_cache_size() { return C.size(); }
/* Only trigger the garbage collector when given limit is exceeded */
void bdd::set_gc_limit(size_t new_gc_limit) { gclimit = new_gc_limit; }
/* Enable/disable the garbage collector depending on given argument */
void bdd::set_gc_enabled(bool new_gc_enabled) { gc_enabled = new_gc_enabled; }

template <typename T>
basic_ostream<T>& bdd::stats(basic_ostream<T>& os) {
	return os << "# S: " << S.size() << " V: "<< V.size() <<
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
	id_map.clear(), S.insert(0), S.insert(1);
//	if (S.size() >= 1e+6) { o::err() << "out of memory" << endl; exit(1); }
	vector<bdd_id> p(V.size(), 0);
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
#define f(i) (SET_BDD_ID(i, (p[GET_BDD_ID(i)] ? p[GET_BDD_ID(i)] : GET_BDD_ID(i))), i)
	for (size_t n = 2; n < V.size(); ++n) {
		DBG(assert(p[GET_BDD_ID(V[n].h)] && p[GET_BDD_ID(V[n].l)]);)
		f(V[n].h), f(V[n].l);
	}
	unordered_map<ite_memo, bdd_ref> c;
	unordered_map<bdds, bdd_ref> am;
	for (pair<ite_memo, bdd_ref> x : C)
		if (	has(S, GET_BDD_ID(x.first.x)) &&
			has(S, GET_BDD_ID(x.first.y)) &&
			has(S, GET_BDD_ID(x.first.z)) &&
			has(S, GET_BDD_ID(x.second)))
			f(x.first.x), f(x.first.y), f(x.first.z),
			x.first.rehash(), c.emplace(x.first, f(x.second));
	C = move(c);
	map<bools, unordered_map<array<bdd_ref, 2>, bdd_ref>, veccmp<bool>> cx;
	unordered_map<array<bdd_ref, 2>, bdd_ref> cc;
	for (const auto& x : CX) {
		for (pair<array<bdd_ref, 2>, bdd_ref> y : x.second)
			if (	has(S, GET_BDD_ID(y.first[0])) &&
				has(S, GET_BDD_ID(y.first[1])) &&
				has(S, GET_BDD_ID(y.second)))
				f(y.first[0]), f(y.first[1]),
				cc.emplace(y.first, f(y.second));
		if (!cc.empty()) cx.emplace(x.first, move(cc));
	}
	CX = move(cx);
	map<pair<bools, bdd_shfts>, unordered_map<array<bdd_ref, 2>, bdd_ref>,
		vec2cmp<bool, bdd_shft>> cxp;
	for (const auto& x : CXP) {
		for (pair<array<bdd_ref, 2>, bdd_ref> y : x.second)
			if (	has(S, GET_BDD_ID(y.first[0])) &&
				has(S, GET_BDD_ID(y.first[1])) &&
				has(S, GET_BDD_ID(y.second)))
				f(y.first[0]), f(y.first[1]),
				cc.emplace(y.first, f(y.second));
		if (!cc.empty()) cxp.emplace(x.first, move(cc));
	}
	CXP = move(cxp);
	unordered_map<bdd_ref, bdd_ref> q;
	map<bools, unordered_map<bdd_ref, bdd_ref>, veccmp<bool>> mex;
	for (const auto& x : memos_ex) {
		for (pair<bdd_ref, bdd_ref> y : x.second)
			if (has(S, GET_BDD_ID(y.first)) && has(S, GET_BDD_ID(y.second)))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mex.emplace(x.first, move(q));
	}
	memos_ex = move(mex);
	map<bdd_shfts, unordered_map<bdd_ref, bdd_ref>, veccmp<bdd_shft>> mp;
	for (const auto& x : memos_perm) {
		for (pair<bdd_ref, bdd_ref> y : x.second)
			if (has(S, GET_BDD_ID(y.first)) && has(S, GET_BDD_ID(y.second)))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mp.emplace(x.first, move(q));
	}
	memos_perm = move(mp);
	map<pair<bdd_shfts, bools>, unordered_map<bdd_ref, bdd_ref>,
		vec2cmp<bdd_shft, bool>> mpe;
	for (const auto& x : memos_perm_ex) {
		for (pair<bdd_ref, bdd_ref> y : x.second)
			if (has(S, GET_BDD_ID(y.first)) && has(S, GET_BDD_ID(y.second)))
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
				if ((b |= !has(S, GET_BDD_ID(i)))) break;
				else f(i);
			if (!b && has(S, GET_BDD_ID(y.second)))
				am.emplace(y.first, f(y.second));
		}
		if (!am.empty()) amx.emplace(x.first, move(am));
	}
	AMX = move(amx);
	map<pair<bools, bdd_shfts>, unordered_map<bdds, bdd_ref>,
		vec2cmp<bool, bdd_shft>> amxp;
	for (const auto& x : AMXP) {
		for (pair<bdds, bdd_ref> y : x.second) {
			b = false;
			for (bdd_ref& i : y.first)
				if ((b |= !has(S, GET_BDD_ID(i)))) break;
				else f(i);
			if (!b && has(S, GET_BDD_ID(y.second)))
				am.emplace(y.first, f(y.second));
		}
		if (!am.empty()) amxp.emplace(x.first, move(am));
	}
	AMXP = move(amxp);
	for (pair<bdds, bdd_ref> x : AM) {
		b = false;
		for (bdd_ref& i : x.first)
			if ((b |= !has(S, GET_BDD_ID(i)))) break;
			else f(i);
		if (!b&&has(S,GET_BDD_ID(x.second))) am.emplace(x.first, f(x.second));
	}
	AM=move(am), bdd_handle::update(p);
	p.clear(), S.clear();
	std::hash<bdd_ref> hsh;
	for (size_t n = 0; n < V.size(); ++n)
		id_map.emplace(bdd_key(hash_upair(hsh(V[n].h), hsh(V[n].l)),
			V[n].h, V[n].l), n);
	OUT(o::dbg() <<"# AM: " << AM.size() << " C: "<< C.size() << endl;)
}

void bdd_handle::update(const vector<bdd_id>& p) {
	unordered_map<bdd_ref, weak_ptr<bdd_handle>> m;
	for (pair<bdd_ref, weak_ptr<bdd_handle>> x : M)
		//DBG(assert(!x.second.expired());) // is this needed?
		if (!x.second.expired())
			f(x.second.lock()->b), m.emplace(f(x.first), x.second);
	M = move(m);
}
#undef f

spbdd_handle bdd_handle::get(bdd_ref  b) {
	DBG(assert((size_t)GET_BDD_ID(b) < V.size());)
	auto it = M.find(b);
	if (it != M.end()) return it->second.lock();
	spbdd_handle h(new bdd_handle(b));
	return M.emplace(b, weak_ptr<bdd_handle>(h)), h;
}

void bdd::bdd_sz(bdd_ref x, set<bdd_ref>& s) {
	if (!s.emplace(x).second) return;
	bdd b = get(x);
	bdd_sz(b.h, s), bdd_sz(b.l, s);
}

spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y) {
	spbdd_handle r = bdd_handle::get(bdd::bdd_and(x->b, y->b));
	return r;
}

spbdd_handle operator%(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_and(x->b, FLIP_INV_OUT(y->b)));
}

spbdd_handle operator||(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_or(x->b, y->b));
}

spbdd_handle bdd_impl(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_or(FLIP_INV_OUT(x->b), y->b));
}

bool bdd_subsumes(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd::bdd_subsumes(x->b, y->b);
}

spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y, cr_spbdd_handle z) {
	return bdd_handle::get(bdd::bdd_ite(x->b, y->b, z->b));
}

spbdd_handle bdd_ite_var(bdd_shft x, cr_spbdd_handle y, cr_spbdd_handle z) {
	return bdd_handle::get(bdd::bdd_ite_var(x, y->b, z->b));
}

spbdd_handle bdd_shift(cr_spbdd_handle x, bdd_shft amt) {
	return bdd_handle::get(bdd::bdd_shift(x->b, amt));
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
	const bdd_shfts& p) {
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
/*	bdd_ref r = F;
	for (auto x : v) r = bdd::bdd_or(r, x->b);
	return bdd_handle::get(r);
	bdds b(v.size());
	for (size_t n = 0; n != v.size(); ++n) b[n] = FLIP_INV_OUT(v[n]->b);
	return bdd_handle::get(FLIP_INV_OUT(bdd::bdd_and_many(move(b))));*/
}

spbdd_handle from_high(bdd_shft s, bdd_ref x) {
	return bdd_handle::get(bdd::add(s + 1, x, F));
}

spbdd_handle from_low(bdd_shft s, bdd_ref y) {
	return bdd_handle::get(bdd::add(s + 1, F, y));
}

spbdd_handle from_high_and_low(bdd_shft s, bdd_ref x, bdd_ref y) {
	return bdd_handle::get(bdd::add(s + 1, x, y));
}

void bdd::sat(bdd_shft v, bdd_shft nvars, bdd_ref  t, bools& p, vbools& r) {
	if (t == F) return;
	if (!leaf(t) && v < var(t))
		p[v - 1] = true, sat(v + 1, nvars, t, p, r),
		p[v - 1] = false, sat(v + 1, nvars, t, p, r);
	else if (v != nvars) {
		p[v - 1] = true, sat(v + 1, nvars, hi(t), p, r),
		p[v - 1] = false, sat(v + 1, nvars, lo(t), p, r);
	} else	r.push_back(p);
}

vbools bdd::allsat(bdd_ref x, bdd_shft nvars) {
	bools p(nvars);
	vbools r;
	return sat(1, nvars + 1, x, p, r), r;
}

vbools allsat(cr_spbdd_handle x, bdd_shft nvars) {
	return bdd::allsat(x->b, nvars);
}

void allsat_cb::sat(bdd_ref x) {
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

bdd_ref bdd::bdd_xor(bdd_ref x, bdd_ref y) { return bdd_ite(x,FLIP_INV_OUT(y),y); }

spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_xor(x->b,y->b));
}

bdd_ref bdd::bdd_ex(bdd_ref x, const bools& b, unordered_map<bdd_ref, bdd_ref>& memo,
	bdd_shft last) {
	if (leaf(x) || var(x) > last+1) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	DBG(assert(var(x)-1 < b.size());)
	if (b[var(x) - 1]) return bdd_ex(bdd_or(hi(x), lo(x)), b, memo, last);
	return memo.emplace(x, bdd::add(var(x), bdd_ex(hi(x), b, memo, last),
				bdd_ex(lo(x), b, memo, last))).first->second;
}

bdd_ref bdd::bdd_ex(bdd_ref x, const bools& b) {
	bdd_shft last = 0;
	for (bdd_shft n = 0; n != b.size(); ++n) if (b[n]) last = n;
	return bdd_ex(x, b, memos_ex[b], last);
}

spbdd_handle operator/(cr_spbdd_handle x, const bools& b) {
	return bdd_handle::get(bdd::bdd_ex(x->b, b));
}

bdd_ref bdd::bdd_permute(bdd_ref x, const bdd_shfts& m,
		unordered_map<bdd_ref, bdd_ref>& memo) {
	if (leaf(x) || m.size() <= var(x)-1) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	return memo.emplace(x, bdd_ite_var(m[var(x)-1],
		bdd_permute(hi(x), m, memo),
		bdd_permute(lo(x), m, memo))).first->second;
}

spbdd_handle operator^(cr_spbdd_handle x, const bdd_shfts& m) {
//	DBG(assert(bdd_nvars(x) < m.size());)
	return bdd_handle::get(bdd::bdd_permute(x->b, m, memos_perm[m]));
}

bdd_ref bdd::bdd_permute_ex(bdd_ref x, const bools& b, const bdd_shfts& m, bdd_shft last,
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

bdd_ref bdd::bdd_permute_ex(bdd_ref x, const bools& b, const bdd_shfts& m) {
	bdd_shft last = 0;
	for (bdd_shft n = 0; n != b.size(); ++n) if (b[n] || (m[n]!=n)) last = n;
	return bdd_permute_ex(x, b, m, last, memos_perm_ex[{m,b}]);
}

spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const bdd_shfts& m) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(x) < m.size());)
	return bdd_handle::get(bdd::bdd_permute_ex(x->b, b, m));
}

spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const bdd_shfts& m) {
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
	return bdd_handle::get(bdd::bdd_and_ex(x->b, FLIP_INV_OUT(y->b), b));
}

spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const bdd_shfts& m) {
//	DBG(assert(bdd_nvars(x) < b.size());)
//	DBG(assert(bdd_nvars(y) < b.size());)
//	DBG(assert(bdd_nvars(x) < m.size());)
//	DBG(assert(bdd_nvars(y) < m.size());)
	return bdd_handle::get(bdd::bdd_and_ex_perm(x->b, FLIP_INV_OUT(y->b), b, m));
}

spbdd_handle from_bit(bdd_shft b, bool v) {
	return bdd_handle::get(bdd::from_bit(b, v));
}

spbdd_handle from_eq(bdd_shft x, bdd_shft y) {
	return bdd_ite(from_bit(x,true), from_bit(y,true), from_bit(y,false));
}

bool bdd::solve(bdd_ref x, bdd_shft v, bdd_ref& l, bdd_ref &h) {
	bools b(v, false);
	b[v-1] = true;
	bdd_ref h_inv = bdd_and_ex(x, from_bit(v, true), b);
	bdd_ref r = bdd_or(l = bdd_and_ex(x, from_bit(v, true), b), h_inv);
	h = FLIP_INV_OUT(h_inv);
	return leaf(r) && !trueleaf(r);
}

array<spbdd_handle, 2> solve(spbdd_handle x, bdd_shft v) {
	bdd_ref h, l;
	if (!bdd::solve(x->b, v, h, l)) return { nullptr, nullptr };
	return { bdd_handle::get(l), bdd_handle::get(h) };
}

void bdd::bdd_nvars(bdd_ref x, set<bdd_shft>& s) {
	if (!leaf(x)) s.insert(var(x)-1), bdd_nvars(hi(x),s),bdd_nvars(lo(x),s);
}

bdd_shft bdd::bdd_nvars(bdd_ref x) {
	if (leaf(x)) return 0;
	set<bdd_shft> s;
	bdd_nvars(x, s);
	bdd_shft r = *s.rbegin();
	return r;
}

bdd_shft bdd_nvars(bdd_handles x) {
	bdd_shft r = 0;
	for (auto y : x) r = max(r, bdd_nvars(y));
	return r;
}

bdd_shft bdd_nvars(spbdd_handle x) { return bdd::bdd_nvars(x->b); }
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

bdd::bdd(bdd_ref h, bdd_ref l) : h(h), l(l) {
//	DBG(assert(V.size() < 2 || (v && h && l));)
}

template <typename T>
basic_ostream<T>& bdd::out(basic_ostream<T>& os, bdd_ref  x) {
	if (leaf(x)) return os << (trueleaf(x) ? 'T' : 'F');
	const bdd b = get(x);
	//return out(out(os << b.v << " ? ", b.h) << " : ", b.l);
	return out(out(os << GET_SHIFT(x) << " ? (", b.h) << ") : (", b.l) << ")";
}

/*
 * #define SATCOUNT
#ifdef SATCOUNT

size_t bdd::satcount_perm(bdd_ref x, bdd_shft leafvar) {
	size_t r = 0;
	if (leaf(x)) return trueleaf(x) ? 1 : 0;
	const bdd bx = get(x);
	bdd_shft hivar = leaf(bx.h) ? leafvar : GET_SHIFT(bx.h);
	bdd_shft lovar = leaf(bx.l) ? leafvar : GET_SHIFT(bx.l);
	r += satcount_perm(bx.h, leafvar) *
		(1 << (hivar - GET_SHIFT(x) - 1));
	r += satcount_perm(bx.l, leafvar) *
		(1 << (lovar - GET_SHIFT(x) - 1));
	return r;
}

static set<bdd_shft> ourvars;
bdd_shft bdd::getvar(bdd_ref x) {
	if (leaf(x)) return 0;
	else {
		ourvars.insert(GET_SHIFT(x));
		const bdd b = get(x);
		return max(GET_SHIFT(x), max(getvar(b.h), getvar(b.l)));
	}
}

// D: this version does a manual 'permute' (in place alligns vars)
// works better with rule(?x ?y ?out) :- headers
// could be buggy (when bdd is minimized, vars removed, we're only guessing)
size_t bdd::satcount_k(bdd_ref x, const bools& ex, const bdd_shfts&) {
	ourvars.clear();
	bdd_shft leafvar = getvar(x) + 1;

	// this's what's missing, if size is smaller means we don't have the 0-var,
	// but this might be correct or not, we might be missing one in the middle?
	size_t k = 1;
	size_t n = count_if(ex.begin(), ex.end(), [](bool isex) { return !isex; });
	if (ourvars.size() < n)
		k = 1 << (n - ourvars.size());

	map<bdd_shft, bdd_shft> inv;
	bdd_shft ivar = 1;
	for (auto x : ourvars) {
		//o::dbg() << "satcount: inv: " << x << ", " << ivar << " ." << endl;
		inv.emplace(x, ivar++);
	}
	leafvar = ivar;

	return k * satcount_k(x, leafvar, inv);
}

size_t bdd::satcount_k(bdd_ref x, bdd_shft leafvar,
	map<bdd_shft, bdd_shft>& mapvars) {
	size_t r = 0;
	if (leaf(x)) {
		return trueleaf(x) ? 1 : 0;
	}
	const bdd bx = get(x);
	bdd_shft hivar = leaf(bx.h) ? leafvar : mapvars.at(GET_SHIFT(bx.h)); // nvars + 1 - GET_SHIFT(x)
	bdd_shft lovar = leaf(bx.l) ? leafvar : mapvars.at(GET_SHIFT(bx.l));
	r += satcount_k(bx.h, leafvar, mapvars) *
		(1 << (hivar - mapvars.at(GET_SHIFT(x)) - 1));
	r += satcount_k(bx.l, leafvar, mapvars) *
		(1 << (lovar - mapvars.at(GET_SHIFT(x)) - 1));
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

void satcount_iter::sat(bdd_ref x) {
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
		DBG(assert(BDD_ABS(x) == T););
		bools np(p.size());
		for (size_t i = 0; i < p.size(); ++i)
			np[i] = !inv[i] ? true : p[i];
		vp.insert(np);
	}
}

#endif
*/
