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
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <set>
#include <map>
#include <array>
#include <iostream>
#include <memory>
#include <functional>
#include "defs.h"

#define hash_pair(x, y) \
	((((size_t)(x)+(size_t)(y))*((size_t)(x)+(size_t)(y)+1)>>1)+(size_t)(y))
#define hash_tri(x, y, z) hash_pair(hash_pair(x, y), z)

class bdd;
typedef std::shared_ptr<class bdd_handle> spbdd_handle;
typedef const spbdd_handle& cr_spbdd_handle;
typedef std::vector<int_t> bdds;
typedef std::vector<spbdd_handle> bdd_handles;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;

struct ite_memo {
	int_t x, y, z;
	size_t hash;
	ite_memo(int_t x, int_t y, int_t z) :
		x(x), y(y), z(z), hash(hash_tri(x, y, z)) {}
	void rehash() { hash = hash_tri(x, y, z); }
	bool operator==(const ite_memo& k) const{return x==k.x&&y==k.y&&z==k.z;}
};

struct bdd_key {
	uint_t hash;
	int_t h, l;
	bdd_key(){}
	bdd_key(uint_t hash, int_t h, int_t l) :
		hash(hash), h(h), l(l) {}
	bool operator==(const bdd_key& k) const { return h==k.h && l==k.l; }
};

template<> struct std::hash<bdd_key> {size_t operator()(const bdd_key&)const;};
template<> struct std::hash<ite_memo>{size_t operator()(const ite_memo&)const;};
template<> struct std::hash<bdds> { size_t operator()(const bdds&) const; };

extern int_t T, F;

spbdd_handle from_bit(uint_t b, bool v);
bool leaf(cr_spbdd_handle h);
bool trueleaf(cr_spbdd_handle h);
std::wostream& out(std::wostream& os, cr_spbdd_handle x);
spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle operator%(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle operator||(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle operator/(cr_spbdd_handle x, const bools& b);
spbdd_handle operator^(cr_spbdd_handle x, const uints& m);
spbdd_handle bdd_impl(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y, cr_spbdd_handle z);
spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y, cr_spbdd_handle z);
spbdd_handle bdd_and_many(const bdd_handles& v);
spbdd_handle bdd_or_many(const bdd_handles& v);
spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const uints& m);
spbdd_handle from_eq(uint_t x, uint_t y);
vbools allsat(cr_spbdd_handle x, uint_t nvars);

class bdd {
	friend class bdd_handle;
	friend class allsat_cb;
	friend spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle operator||(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle operator%(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle operator/(cr_spbdd_handle x, const bools& b);
	friend spbdd_handle operator^(cr_spbdd_handle x, const uints& m);
	friend spbdd_handle bdd_impl(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y,
		cr_spbdd_handle z);
	friend spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y,
		cr_spbdd_handle z);
	friend spbdd_handle bdd_and_many(const bdd_handles& v);
	friend spbdd_handle bdd_or_many(const bdd_handles& v);
	friend spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b,
		const uints& m);
	friend vbools allsat(cr_spbdd_handle x, uint_t nvars);
	friend spbdd_handle from_bit(uint_t b, bool v);
	friend bool leaf(cr_spbdd_handle h);
	friend bool trueleaf(cr_spbdd_handle h);
	friend std::wostream& out(std::wostream& os, cr_spbdd_handle x);

	static std::vector<std::unordered_map<bdd_key, int_t>> Mp;
	static std::vector<std::unordered_map<bdd_key, int_t>> Mn;
	static std::unordered_map<ite_memo, int_t> C;
	static std::unordered_map<bdds, int_t> AM;
	static std::unordered_set<int_t> S;

	inline static int_t hi(int_t x) {
		return	x < 0 ? V[-x].v < 0 ? -V[-x].l : -V[-x].h
			: V[x].v < 0 ? V[x].l : V[x].h;
	}

	inline static int_t lo(int_t x) {
		return	x < 0 ? V[-x].v < 0 ? -V[-x].h : -V[-x].l
			: V[x].v < 0 ? V[x].h : V[x].l;
	}

	inline static uint_t var(int_t x) { return abs(V[abs(x)].v); }

	inline static bdd get(int_t x) {
		if (x > 0) {
			const bdd &y = V[x];
			return y.v > 0 ? y : bdd(-y.v, y.l, y.h);
		}
		const bdd &y = V[-x];
		return y.v > 0 ? bdd(y.v, -y.h, -y.l) : bdd(-y.v, -y.l, -y.h);
	}

	static int_t bdd_and(int_t x, int_t y);
	static int_t bdd_or(int_t x, int_t y) { return -bdd_and(-x, -y); }
	static int_t bdd_ite(int_t x, int_t y, int_t z);
	static int_t bdd_ite_var(uint_t x, int_t y, int_t z);
	static int_t bdd_and_many(bdds v);
	static int_t bdd_ex(int_t x, const bools& b,
		std::unordered_map<int_t, int_t>& memo);
	static int_t bdd_permute(const int_t& x, const uints& m,
		std::unordered_map<int_t, int_t>& memo);
	static int_t bdd_permute_ex(int_t x, const bools& b, const uints& m,
		size_t last, std::unordered_map<int_t, int_t>& memo);
	static int_t bdd_permute_ex(int_t x, const bools& b, const uints& m);
	static void mark_all(int_t i);
	static size_t bdd_and_many_iter(bdds, bdds&, bdds&, int_t&, size_t&);
	static void sat(uint_t v, uint_t nvars, int_t t, bools& p, vbools& r);
	static vbools allsat(int_t x, uint_t nvars);
	static bool am_simplify(bdds& v);
	inline static int_t add(int_t v, int_t h, int_t l) {
		DBG(assert(h && l && v > 0);)
		DBG(assert(leaf(h) || v < abs(V[abs(h)].v));)
		DBG(assert(leaf(l) || v < abs(V[abs(l)].v));)
//		DBG(assert(M.size() == V.size());)
		if (h == l) return h;
		if (h > l) std::swap(h, l), v = -v;
		static std::unordered_map<bdd_key, int_t>::const_iterator it;
		static bdd_key k;
		auto &mm = v < 0 ? Mn : Mp;
		if (mm.size() <= (size_t)abs(v)) mm.resize(abs(v)+1);
		auto &m = mm[abs(v)];
		if (l < 0) {
			k = bdd_key(hash_pair(-h, -l), -h, -l);
			return	(it = m.find(k)) != m.end() ? -it->second :
				(V.emplace_back(v, -h, -l),
				m.emplace(std::move(k), V.size()-1),
				-V.size()+1);
		}
		k = bdd_key(hash_pair(h, l), h, l);
		return	(it = m.find(k)) != m.end() ? it->second :
			(V.emplace_back(v, h, l),
			m.emplace(std::move(k), V.size()-1),
			V.size()-1);
	}

	inline static int_t from_bit(uint_t b, bool v);
	inline static bool leaf(int_t t) { return abs(t) == T; }
	inline static bool trueleaf(int_t t) { return t > 0; }
//	void rehash() { hash = hash_tri(v, h, l); }
	static std::wostream& out(std::wostream& os, int_t x);
	int_t h, l, v;
public:
//	bdd() {}
	bdd(int_t v, int_t h, int_t l);
//	bdd_key getkey() const { return bdd_key(hash, v, h, l); }
	inline bool operator==(const bdd& b) const {
		return v == b.v && h == b.h && l == b.l;
	}
	static std::vector<bdd> V;
	static void init();
	static void gc();
};

class bdd_handle {
	friend class bdd;
	bdd_handle(int_t b) : b(b) { }//bdd::mark(b); }
	static void update(const std::vector<int_t>& p);
	static std::unordered_map<int_t, std::weak_ptr<bdd_handle>> M;
public:
	int_t b;
	static spbdd_handle get(int_t b);
	static spbdd_handle T, F;
	~bdd_handle() {
		//if (abs(b) > 1 && (M.erase(b), !has(M, -b))) bdd::unmark(b);
		if (abs(b) > 1) M.erase(b);//, !has(M, -b))) bdd::unmark(b);
	}
};

class allsat_cb {
public:
	typedef std::function<void(const bools&, int_t)> callback;
	allsat_cb(cr_spbdd_handle r, uint_t nvars, callback f) :
		r(r->b), nvars(nvars), f(f), p(nvars) {}
	void operator()() { sat(r); }
private:
	int_t r;
	const uint_t nvars;
	uint_t v = 1;
	callback f;
	bools p;
	void sat(int_t x);
};
