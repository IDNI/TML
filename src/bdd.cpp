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
using namespace std;

int_t T, F;
unordered_map<bdd::key, int_t> bdd::M;
vector<bdd> bdd::V;
unordered_map<ite_memo, int_t> bdd::C;
unordered_map<bdds, int_t> bdd::AM;
unordered_set<int_t> bdd::S;
unordered_map<int_t, weak_ptr<bdd_handle>> bdd_handle::M;
spbdd_handle bdd_handle::T, bdd_handle::F;
map<bools, unordered_map<int_t, int_t>> memos_ex;
map<uints, unordered_map<int_t, int_t>> memos_perm;
map<pair<uints, bools>, unordered_map<int_t, int_t>> memos_perm_ex;

void bdd::init() {
	V.emplace_back(0, 0, 0), // dummy
	V.back().rehash(), T = 1, F = -1,
	V.emplace_back(0, 1, 1), V.back().rehash(),
	M.emplace(V.back().getkey(), 1), mark(0), mark(T), mark(F),
	bdd_handle::T = bdd_handle::get(T), bdd_handle::F = bdd_handle::get(F);
}

int_t bdd::add(uint_t v, int_t h, int_t l) {
	assert(v && h && l);
	if (h == l) return h;
	if (l < 0) {
		key k = { hash_tri(v, -h, -l), v, -h, -l };
		auto it = M.find(k);
		if (it != M.end()) return -it->second;
		V.emplace_back(v, -h, -l), M.emplace(k, V.size() - 1);
		return -V.size() + 1;
	}
	key k = { hash_tri(v, h, l), v, h, l };
	auto it = M.find(k);
	if (it != M.end()) return it->second;
	V.emplace_back(v, h, l), M.emplace(k, V.size() - 1);
	return V.size() - 1;
}

int_t bdd::from_bit(uint_t b, bool v) {
	return v ? add(b + 1, T, F) : add(b + 1, F, T);
}

int_t bdd::bdd_and(int_t x, int_t y) {
	assert(x && y);
	if (x == F || y == F) return F;
	if (x == T || x == y) return y;
	if (y == T) return x;
	if (x == -y) return F;
	if (x > y) swap(x, y);
	auto it = C.find({x,y,F});
	if (it != C.end()) return it->second;
	const uint_t vx = V[abs(x)].v, vy = V[abs(y)].v;
	int_t r;
	if (vx < vy) r = add(vx, bdd_and(hi(x), y), bdd_and(lo(x), y));
	else if (vx > vy) r = add(vy, bdd_and(x, hi(y)), bdd_and(x, lo(y)));
	else r = add(vx, bdd_and(hi(x), hi(y)), bdd_and(lo(x), lo(y)));
	return C.emplace(ite_memo{x,y,F}, r), r;
}

int_t bdd::bdd_ite_var(uint_t x, int_t y, int_t z) {
	return bdd_ite(from_bit(x, true), y, z);
}

int_t bdd::bdd_ite(int_t x, int_t y, int_t z) {
	assert(x && y && z);
	if (x < 0) return bdd_ite(-x, z, y);
	if (x == F) return z;
	if (x == T || y == z) return y;
	if (x == -y || x == z) return F;
	auto it = C.find({x, y, z});
	if (it != C.end()) return it->second;
	int_t r;
	const uint_t vx = V[abs(x)].v, vy = V[abs(y)].v, vz = V[abs(z)].v;
	const uint_t s = min(vx, min(vy, vz));
	if (y == T) r = bdd_or(x, z);
	else if (y == F) r = bdd_and(-x, z);
	else if (z == F) r = bdd_and(x, y);
	else if (z == T) r = bdd_or(-x, y);
	else if (vx == vy && vy == vz)
		r =	add(vx, bdd_ite(hi(x), hi(y), hi(z)),
				bdd_ite(lo(x), lo(y), lo(z)));
	else if (s == vx && s == vy)
		r =	add(vx, bdd_ite(hi(x), hi(y), z),
				bdd_ite(lo(x), lo(y), z));
	else if (s == vy && s == vz)
		r =	add(vy, bdd_ite(x, hi(y), hi(z)),
				bdd_ite(x, lo(y), lo(z)));
	else if (s == vx && s == vz)
		r =	add(vx, bdd_ite(hi(x), y, hi(z)),
				bdd_ite(lo(x), y, lo(z)));
	else if (s == vx)
		r =	add(vx, bdd_ite(hi(x), y, z), bdd_ite(lo(x), y, z));
	else if (s == vy)
		r =	add(vy, bdd_ite(x, hi(y), z), bdd_ite(x, lo(y), z));
	else	r =	add(vz, bdd_ite(x, y, hi(z)), bdd_ite(x, y, lo(z)));
	return C.emplace(ite_memo{x, y, z}, r), r;
}

void bdd::mark_all(int_t i) {
	if (S.find(i = abs(i)) != S.end()) return;
	S.insert(i), mark(hi(i)), mark(lo(i));
}

size_t bdd::bdd_and_many_iter(bdds v, bdds& h, bdds& l, int_t &res, size_t &m) {
	size_t i;
	int_t t;
	bool b, eq, flag;
	bdds x;
	if (v.empty()) return res = T, 1;
	if (v.size() == 2) return res = bdd_and(v[0], v[1]), 1;
	for (size_t n = 0; n < v.size();)
		if (!leaf(v[n])) ++n;
		else if (!trueleaf(v[n])) return res = F, 1;
		else if (v.erase(v.begin()+n), v.size()==1) return res=v[0], 1;
		else if (v.size() == 2) return res = bdd_and(v[0], v[1]), 1;
		else if (v.empty()) return res = T, 1;
		else ++n;
	m = var(v[0]), t = v[0];
	b = false, eq = true, flag = false;
	for (i = 1; i != v.size(); ++i)
		if (!leaf(v[i])) {
			b |= var(v[i]) != m, eq &= t == v[i];
			if (var(v[i]) < m) m = var(v[i]);
		} else if (!trueleaf(v[i])) return res = F, 1;
	if (eq) return res = t, 1;
	for (i = 0; i != v.size(); ++i)
		if (b && var(v[i]) != m) h.push_back(v[i]);
		else if (!leaf(hi(v[i]))) h.push_back(hi(v[i]));
		else if (!trueleaf(hi(v[i]))) { flag = true; break; }
	for (i = 0; i != v.size(); ++i)
		if (b && var(v[i]) != m) l.push_back(v[i]);
		else if (!leaf(lo(v[i]))) l.push_back(lo(v[i]));
		else if (!trueleaf(lo(v[i]))) return flag ? res = F, 1 : 2;
	auto f = [](int_t x, int_t y) { return abs(x) < abs(y); };
	sort(h.begin(), h.end(), f), sort(l.begin(), l.end(), f);
	if (!flag) {
		for (size_t n = 1; n < h.size();)
			if (h[n] == -h[n-1]) { flag = true; break; }
			else if (h[n] == h[n-1]) {
				h.erase(h.begin() + n);
				if (h.empty()) { flag = true; break; }
				if (h.size() == 1) break;
			} else ++n;
	}
	for (size_t n = 1; n < l.size();)
		if (l[n] == -l[n-1]) return flag ? 3 : 0;
		else if (l[n] == l[n-1]) {
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
		int_t r = bdd_and_many(move(x));
		if (r == F) return res = F, 1;
		h.push_back(r), l.push_back(r);
	}
	return 0;
}

int_t bdd::bdd_and_many(bdds v) {
	static unordered_map<ite_memo, int_t>::const_iterator jt;
	for (size_t n = 0; n < v.size(); ++n)
		for (size_t k = 0; k < n; ++k) {
			int_t x, y;
			if (v[n] < v[k]) x = v[n], y = v[k];
			else x = v[k], y = v[n];
			if ((jt = C.find({x, y, F})) != C.end()) {
				v.erase(v.begin()+k), v.erase(v.begin()+n-1),
				v.push_back(jt->second), n = k = 0;
				break;
			}
		}
	if (v.empty()) return T;
	if (v.size() == 1) return v[0];
	if (v.size() == 2) return bdd_and(v[0], v[1]);
	auto it = AM.find(v);
	if (it != AM.end()) return it->second;
//	onmemo();
	int_t res = F, h, l;
	size_t m = 0;
	bdds vh, vl;
	switch (bdd_and_many_iter(move(v), vh, vl, res, m)) {
		case 0: l = bdd_and_many(move(vl)),
			h = bdd_and_many(move(vh));
			break;
		case 1: return AM.emplace(v, res), res;
		case 2: h = bdd_and_many(move(vh)), l = F; break;
		case 3: h = F, l = bdd_and_many(move(vl)); break;
		default: throw 0;
	}
	return AM.emplace(v, bdd::add(m, h, l)).first->second;
}

void bdd::gc() {
	if (V.size() / S.size() < 2) return;
	for (int_t i : S) mark_all(i);
	unordered_set<int_t> G;
	for (size_t n = 0; n != V.size(); ++n)
		if (S.find(n) == S.end())
			G.insert(n);
	assert(!G.empty());
	vector<int_t> p(V.size(), 0);
	for (size_t n = 0, k = 0; n != V.size(); ++n)
		if (G.find(n) != G.end())
			p[V.size() - ++k] = n, V[n] = V[V.size() - k];
	wcout << G.size() << ' ' << V.size() << endl;
	M.clear(), V.resize(V.size() - G.size());
#define f(i) (i = (i >= 0 ? p[i] ? p[i] : i : p[-i] ? -p[-i] : i))
	for (size_t n = 2; n != V.size(); ++n)
		f(V[n].h), f(V[n].l), V[n].rehash();
	unordered_map<ite_memo, int_t> c;
	unordered_map<bdds, int_t> am;
	for (pair<ite_memo, int_t> x : C)
		if (!(	has(G, abs(x.first[0])) ||
			has(G, abs(x.first[1])) ||
			has(G, abs(x.first[2])) ||
			has(G, abs(x.second))))
			f(x.first[0]), f(x.first[1]), f(x.first[2]),
			c.emplace(x.first, f(x.second));
	unordered_map<int_t, int_t> q;
	map<bools, unordered_map<int_t, int_t>> mex;
	map<uints, unordered_map<int_t, int_t>> mp;
	for (const auto& x : memos_ex) {
		for (pair<int_t, int_t> y : x.second)
			if (!has(G, abs(y.first)) && !has(G, abs(y.second)))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mex.emplace(x.first, move(q));
	}
	memos_ex = move(mex);
	for (const auto& x : memos_perm) {
		for (pair<int_t, int_t> y : x.second)
			if (!has(G, abs(y.first)) && !has(G, abs(y.second)))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mp.emplace(x.first, move(q));
	}
	memos_perm = move(mp);
	map<pair<uints, bools>, unordered_map<int_t, int_t>> mpe;
	for (const auto& x : memos_perm_ex) {
		for (pair<int_t, int_t> y : x.second)
			if (!has(G, abs(y.first)) && !has(G, abs(y.second)))
				q.emplace(f(y.first), f(y.second));
		if (!q.empty()) mpe.emplace(x.first, move(q));
	}
	memos_perm_ex = move(mpe);
	bool b;
	for (pair<bdds, int_t> x : AM) {
		b = false;
		for (int_t& i : x.first)
			if ((b |= has(G, abs(i)))) break;
			else f(i);
		if (b || has(G, abs(x.second))) continue;
		f(x.second), am.emplace(x.first, x.second);
	}
	wcout << c.size() << ' ' << C.size();
	bdd_handle::update(p, G);
	C = move(c), AM = move(am), G.clear();
	for (size_t n = 0; n < V.size(); ++n) M.emplace(V[n].getkey(), n);
	wcout << ' ' << V.size() << endl;
}

void bdd_handle::update(const vector<int_t>& p, const unordered_set<int_t>&
		DBG(G)) {
	std::unordered_map<int_t, std::weak_ptr<bdd_handle>> m;
	for (pair<int_t, std::weak_ptr<bdd_handle>> x : m) {
		DBG(assert(!has(G, x.first));)
		f(x.first), f(x.second.lock()->b), m.emplace(x.first,x.second);
	}
	M = move(m);
}
#undef f

spbdd_handle bdd_handle::get(int_t b) {
	auto it = M.find(b);
	if (it != M.end()) return it->second.lock();
	spbdd_handle h(new bdd_handle(b));
	return	M.emplace(b, std::weak_ptr<bdd_handle>(h)), h;
}

spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y) {
	return bdd_handle::get(bdd::bdd_and(x->b, y->b));
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

spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y, cr_spbdd_handle z) {
	return bdd_handle::get(bdd::bdd_ite(x->b, y->b, z->b));
}

spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y, cr_spbdd_handle z) {
	return bdd_handle::get(bdd::bdd_ite_var(x, y->b, z->b));
}

spbdd_handle bdd_and_many(const bdd_handles& v) {
	bdds b(v.size());
	for (size_t n = 0; n != v.size(); ++n) b[n] = v[n]->b;
	return bdd_handle::get(bdd::bdd_and_many(move(b)));
}

spbdd_handle bdd_or_many(const bdd_handles& v) {
	int_t r = F;
	for (auto x : v) r = bdd::bdd_or(r, x->b);
	return bdd_handle::get(r);
	bdds b(v.size());
	for (size_t n = 0; n != v.size(); ++n) b[n] = -v[n]->b;
	return bdd_handle::get(-bdd::bdd_and_many(move(b)));
}

void bdd::sat(uint_t v, uint_t nvars, int_t t, bools& p, vbools& r) {
	if (t == F) return;
	if (!leaf(t) && v < var(t))
		p[v - 1] = true, sat(v + 1, nvars, t, p, r),
		p[v - 1] = false, sat(v + 1, nvars, t, p, r);
	else if (v != nvars) {
		p[v - 1] = true, sat(v + 1, nvars, hi(t), p, r),
		p[v - 1] = false, sat(v + 1, nvars, lo(t), p, r);
	} else	r.push_back(p);
}

vbools bdd::allsat(int_t x, uint_t nvars) {
	bools p(nvars);
	vbools r;
	return sat(1, nvars + 1, x, p, r), r;
}

vbools allsat(cr_spbdd_handle x, uint_t nvars) {
	return bdd::allsat(x->b, nvars);
}

void allsat_cb::sat(int_t x) {
	if (x == F) return;
	else if (!bdd::leaf(x) && v < bdd::var(x)) {
		DBG(assert(bdd::var(x) <= nvars);)
		p[++v-2] = true, sat(x), p[v-2] = false, sat(x), --v;
	} else if (v != nvars + 1)
		p[++v-2] = true, sat(bdd::hi(x)),
		p[v-2] = false, sat(bdd::lo(x)), --v;
	else f(p, x);
}

int_t bdd::bdd_ex(int_t x, const bools& b, unordered_map<int_t, int_t>& memo){
	if (leaf(x)) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	int_t r, y = x;
	while (var(y) - 1 < b.size() && b[var(y) - 1]) {
		r = bdd_or(hi(y), lo(y));
		if (leaf(r)) return memo.emplace(y, r), r;
		y = r;
	}
	if (var(y) - 1 >= b.size()) return y;
	return memo.emplace(y, bdd::add(var(y), bdd_ex(hi(y), b, memo),
				bdd_ex(lo(y), b, memo))).first->second;
}

spbdd_handle operator/(cr_spbdd_handle x, const bools& b) {
	return bdd_handle::get(bdd::bdd_ex(x->b, b, memos_ex[b]));
}

int_t bdd::bdd_permute(const int_t& x, const uints& m,
		unordered_map<int_t, int_t>& memo) {
	if (leaf(x)) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	return memo.emplace(x, bdd_ite_var(m[var(x)-1],
		bdd_permute(hi(x), m, memo),
		bdd_permute(lo(x), m, memo))).first->second;
}

spbdd_handle operator^(cr_spbdd_handle x, const uints& m) {
	return bdd_handle::get(bdd::bdd_permute(x->b, m, memos_perm[m]));
}

int_t bdd::bdd_permute_ex(int_t x, const bools& b, const uints& m, size_t last,
	unordered_map<int_t, int_t>& memo) {
	if (leaf(x) || var(x) > last + 1) return x;
	auto it = memo.find(x);
	if (it != memo.end()) return it->second;
	int_t t = x, y = x;
	DBG(assert(b.size() >= var(x));)
	for (int_t r; var(y)-1 < b.size() && b[var(y)-1]; y = r)
		if (leaf((r = bdd_or(hi(y), lo(y)))))
			return memo.emplace(t, r), r;
		DBG(else assert(b.size() >= var(r));)
	DBG(assert(!leaf(y) && m.size() >= var(y));)
	return	memo.emplace(t, bdd_ite_var(m[var(y)-1],
		bdd_permute_ex(hi(y), b, m, last, memo),
		bdd_permute_ex(lo(y), b, m, last, memo))).first->second;
}

int_t bdd::bdd_permute_ex(int_t x, const bools& b, const uints& m) {
	size_t last = 0;
	for (size_t n = 0; n != b.size(); ++n) if (b[n] || m[n] != n) last = n;
	return bdd_permute_ex(x, b, m, last, memos_perm_ex[{m,b}]);
}

spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const uints& m) {
	return bdd_handle::get(bdd::bdd_permute_ex(x->b, b, m));
}

spbdd_handle bdd_handle::get(uint_t v, cr_spbdd_handle h, cr_spbdd_handle l) {
	return get(bdd::add(v, h->b, l->b));
}

spbdd_handle from_bit(uint_t b, bool v) {
	return bdd_handle::get(bdd::from_bit(b, v));
}

spbdd_handle from_eq(uint_t x, uint_t y) {
	return bdd_ite(from_bit(x,true), from_bit(y,true), from_bit(y,false));
}

bool leaf(cr_spbdd_handle h) { return bdd::leaf(h->b); }
bool trueleaf(cr_spbdd_handle h) { return bdd::trueleaf(h->b); }
wostream& out(wostream& os, cr_spbdd_handle x) { return bdd::out(os, x->b); }

size_t std::hash<ite_memo>::operator()(const ite_memo& m) const {
	return hash_pair(m[0], hash_pair(m[1], m[2]));
}

size_t std::hash<std::tuple<uint_t, uint_t, int_t, int_t>>::operator()(
	const std::tuple<uint_t,uint_t,int_t,int_t>& k) const {
	return std::get<0>(k);
}

size_t std::hash<bdds>::operator()(const bdds& b) const {
	size_t r = 0;
	for (int_t i : b) r += i >= 0 ? bdd::V[i].hash : -bdd::V[-i].hash;
	return r;
}

bdd::bdd(uint_t v, int_t h, int_t l) : h(h), l(l), v(v) { rehash(); }

wostream& bdd::out(wostream& os, int_t x) {
	if (leaf(x)) return os << (trueleaf(x) ? L'T' : L'F');
	if (x < 0) x = -x, os << L'~';
	const bdd& b = V[x];
	return out(out(os << b.v << L" ? ", b.h) << L" : ", b.l);
}

/*wostream& operator<<(wostream& os, const bools& x) {
	for (auto y : x) os << (y ? 1 : 0);
	return os;
}

wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y : x) os << y << endl;
	return os;
}

spbdd_handle rand_bdd(int_t n = 5) {
	if (!n) return bdd_ite(
			from_bit(random()%10, random()&1),
			from_bit(random()%10, random()&1),
			from_bit(random()%10, random()&1));
	return bdd_ite(rand_bdd(n-1), rand_bdd(n-1), rand_bdd(n-1));
}

void test_and_many() {
	set<spbdd_handle> s;
	for (size_t k = 0; k != 100; ++k) {
		bdd_handles b;
		for (size_t n = 0; n != 8; ++n) b.push_back(rand_bdd());
		spbdd_handle r = bdd_handle::T;
		for (cr_spbdd_handle i : b) r = r && i;
		assert(r == bdd_and_many(b));
		cout<<k<<endl;
		if (random()&1) s.insert(r);
	}
}*/
