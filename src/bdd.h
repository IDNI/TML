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

#define fpairing(x, y) \
	((((size_t)(x)+(size_t)(y))*((size_t)(x)+(size_t)(y)+1)>>1)+(size_t)(y))
#define neg_to_odd(x) (((x)<0?(((-(x))<<1)+1):((x)<<1)))
#define hash_pair(x, y) fpairing(neg_to_odd(x), neg_to_odd(y))
#define hash_tri(x, y, z) fpairing(hash_pair(x, y), neg_to_odd(z))

class bdd;
typedef std::shared_ptr<class bdd_handle> spbdd_handle;
typedef const spbdd_handle& cr_spbdd_handle;
typedef std::vector<int_t> bdds;
typedef std::vector<spbdd_handle> bdd_handles;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;

const int_t T = 1, F = -1;

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
template<> struct std::hash<std::array<int_t, 2>>{
	size_t operator()(const std::array<int_t, 2>&) const;
};
template<> struct std::hash<bdds> { size_t operator()(const bdds&) const; };

//const int_t T = 1, F = -1;

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
bool bdd_subsumes(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y, cr_spbdd_handle z);
spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y, cr_spbdd_handle z);
spbdd_handle bdd_and_many(bdd_handles v);
spbdd_handle bdd_and_many_ex(bdd_handles v, const bools& ex);
spbdd_handle bdd_or_many(const bdd_handles& v);
spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools& b);
spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools&);
spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m);
spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m);
spbdd_handle bdd_not_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools&);
spbdd_handle bdd_not_and_not_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m);
spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const bools& b, const uints&);
spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const uints& m);
spbdd_handle from_eq(uint_t x, uint_t y);
int_t bdd_or_reduce(bdds b);
size_t bdd_nvars(spbdd_handle x);
size_t bdd_nvars(bdd_handles x);
vbools allsat(cr_spbdd_handle x, uint_t nvars);
extern std::vector<class bdd> V;
extern std::unordered_map<ite_memo, int_t> C;
extern std::vector<std::unordered_map<bdd_key, int_t>> Mp, Mn;

struct xynode {
	int_t x = 0, y = 0;
	int_t prod = std::numeric_limits<int>::max();
	xynode() {} // for stack allocation
	xynode(int_t x_, int_t y_) : x(x_), y(y_) {
		calctail();
	}
	//((x - F) * (y - F) * (x + y) == 0) => F;
	//((x + F) * (y + F) * (x - y) == 0) => x == y ? y : x * y
	inline void calctail() {
		if (x == F || y == F || x == -y) prod = F;
		else if (x == T || x == y) prod = y;
		else if (y == T) prod = x;
		else {
			if (x > y) std::swap(x, y);
			ite_memo m = { x, y, F };
			auto it = C.find(m);
			if (it != C.end()) prod = it->second;
			else prod = std::numeric_limits<int>::max(); // ?
		}
	}
};

enum class StackState {
	Tail,
	Left,
	Right,
	Add
};

struct xyitem {
	xynode node;
	StackState state;
	xynode right;
	int_t val = 0, leftval = 0, rightval = 0;
	xyitem() {} // for stack allocation
	xyitem(const xynode& node, StackState state) :
		node(node), state(state), right() {
	}
};

#pragma pack(push, 1)
struct xystackitem {
	int_t x = 0, y = 0, tailval = std::numeric_limits<int>::max();
	int_t state;
	int_t rx = 0, ry = 0, rtailval = std::numeric_limits<int>::max();
	int_t val = 0, leftval = 0, rightval = 0;
	//xystackitem() {} // for stack allocation
};
#pragma pack(pop)

class bdd {
	friend class bdd_handle;
	friend class allsat_cb;
	friend struct sbdd_and_many_ex;
	friend struct sbdd_and_ex_perm;
	friend struct sbdd_and_many_ex_perm;
	friend spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle operator||(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle operator%(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle operator/(cr_spbdd_handle x, const bools& b);
	friend spbdd_handle operator^(cr_spbdd_handle x, const uints& m);
	friend spbdd_handle bdd_impl(cr_spbdd_handle x, cr_spbdd_handle y);
	friend bool bdd_subsumes(cr_spbdd_handle x, cr_spbdd_handle y);
	friend int_t bdd_or_reduce(bdds b);
	friend spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y,
		cr_spbdd_handle z);
	friend spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y,
		cr_spbdd_handle z);
	friend spbdd_handle bdd_and_many(bdd_handles v);
	friend spbdd_handle bdd_and_many_ex(bdd_handles v, const bools& ex);
	friend spbdd_handle bdd_or_many(const bdd_handles& v);
	friend spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b,
		const uints& m);
	friend spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle,
		const bools& b, const uints& m);
	friend spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x,
		cr_spbdd_handle, const bools& b, const uints& m);
	friend spbdd_handle bdd_not_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools&);
	friend spbdd_handle bdd_not_and_not_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools& b, const uints& m);
	friend spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const bools& b,
		const uints&);
	friend spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools& b);
	friend spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools&);
	friend vbools allsat(cr_spbdd_handle x, uint_t nvars);
	friend spbdd_handle from_bit(uint_t b, bool v);
	friend size_t bdd_nvars(spbdd_handle x);
	friend bool leaf(cr_spbdd_handle h);
	friend bool trueleaf(cr_spbdd_handle h);
	friend std::wostream& out(std::wostream& os, cr_spbdd_handle x);

	inline static bdd get(int_t x) {
		if (x > 0) {
			const bdd &y = V[x];
			return y.v > 0 ? y : bdd(-y.v, y.l, y.h);
		}
		const bdd &y = V[-x];
		return y.v > 0 ? bdd(y.v, -y.h, -y.l) : bdd(-y.v, -y.l, -y.h);
	}

	// x  y  =		x  y  =
	// F     F		T  y  y
	//    F  F		x  T  x
	// x -x  F		x  x  x
	// (x - F) * (y - F) * (x + y) == 0 => F
	// (x + F) * (y + F) * (x - y) == 0 => x == y ? y : x * y
	// pull out the exit condition in one place, it's mutable (x,y) for simplicity
	inline static int_t calctailval(int& x, int& y) {
		if (x == F || y == F || x == -y) return F;
		if (x == T || x == y) return y;
		if (y == T) return x;
		if (x > y) std::swap(x, y);
		ite_memo m = { x, y, F };
		auto it = C.find(m);
		if (it != C.end()) return it->second;
		return std::numeric_limits<int>::max();
	}

	static int_t and_stack_ints(const int_t x, const int_t y);
	static int_t and_stack(const int_t x, const int_t y);

	static int_t bdd_and(int_t x, int_t y);
	static int_t bdd_and_recursive(int_t x, int_t y);

	static int_t bdd_and_ex(int_t x, int_t y, const bools& ex);
	static int_t bdd_and_ex(int_t x, int_t y, const bools& ex,
		std::unordered_map<std::array<int_t, 2>, int_t>& memo,
		std::unordered_map<int_t, int_t>& memo2, int_t last);
	static int_t bdd_or(int_t x, int_t y) { return -bdd_and(-x, -y); }
	static int_t bdd_ite(int_t x, int_t y, int_t z);
	static int_t bdd_ite_var(uint_t x, int_t y, int_t z);
	static int_t bdd_and_many(bdds v);
	static int_t bdd_and_many_ex(bdds v, const bools& ex);
	static int_t bdd_and_many_ex(bdds v, const bools& ex,
		std::unordered_map<bdds, int_t>& memo,
		std::unordered_map<int_t, int_t>& m2,
		std::unordered_map<std::array<int_t, 2>, int_t>& m3);
	static int_t bdd_ex(int_t x, const bools& b,
		std::unordered_map<int_t, int_t>& memo, int_t last);
	static int_t bdd_ex(int_t x, const bools& b);
	static int_t bdd_permute(const int_t& x, const uints& m,
		std::unordered_map<int_t, int_t>& memo);
	static int_t bdd_permute_ex(int_t x, const bools& b, const uints& m,
		size_t last, std::unordered_map<int_t, int_t>& memo);
	static int_t bdd_permute_ex(int_t x, const bools& b, const uints& m);
	static void mark_all(int_t i);
	static size_t bdd_and_many_iter(bdds, bdds&, bdds&, int_t&, size_t&);
	static char bdd_and_many_ex_iter(const bdds&v, bdds& h, bdds& l,
		int_t &m);
	static int_t bdd_and_ex_perm(int_t x, int_t y, const bools& ex,
		const uints&);
	static int_t bdd_and_many_ex_perm(bdds v, const bools&, const uints&);
	static void sat(uint_t v, uint_t nvars, int_t t, bools& p, vbools& r);
	static vbools allsat(int_t x, uint_t nvars);
	static bool am_simplify(bdds& v,const std::unordered_map<bdds, int_t>&);
	static void bdd_sz(int_t x, std::set<int_t>& s);
	static void bdd_nvars(int_t x, std::set<int_t>& s);
	static size_t bdd_nvars(int_t x);
	static bool bdd_subsumes(int_t x, int_t y);

	//inline static int_t add(int_t v, int_t h, int_t l);
	inline static int_t add(int_t v, int_t h, int_t l) {
		DBG(assert(h && l && v > 0);)
		DBG(assert(leaf(h) || v < abs(V[abs(h)].v));)
		DBG(assert(leaf(l) || v < abs(V[abs(l)].v));)
		if (h == l) return h;
		if (abs(h) < abs(l)) std::swap(h, l), v = -v;
		static std::unordered_map<bdd_key, int_t>::const_iterator it;
		static bdd_key k;
		auto& mm = v < 0 ? Mn : Mp;
		if (mm.size() <= (size_t)abs(v)) mm.resize(abs(v) + 1);
		auto& m = mm[abs(v)];
		if (l < 0) {
			k = bdd_key(hash_pair(-h, -l), -h, -l);
			return	(it = m.find(k)) != m.end() ? -it->second :
				(V.emplace_back(v, -h, -l),
					m.emplace(std::move(k), V.size() - 1),
					-V.size() + 1);
		}
		k = bdd_key(hash_pair(h, l), h, l);
		return	(it = m.find(k)) != m.end() ? it->second :
			(V.emplace_back(v, h, l),
				m.emplace(std::move(k), V.size() - 1),
				V.size() - 1);
	}

	inline static int_t from_bit(uint_t b, bool v);
	inline static bool leaf(int_t t) { return abs(t) == T; }
	inline static bool trueleaf(int_t t) { return t > 0; }
	static std::wostream& out(std::wostream& os, int_t x);
	int_t h, l, v;
public:
	bdd(int_t v, int_t h, int_t l);
	inline bool operator==(const bdd& b) const {
		return v == b.v && h == b.h && l == b.l;
	}
	static void init();
	static void gc();
	inline static int_t hi(int_t x) {
		return	x < 0 ? V[-x].v < 0 ? -V[-x].l : -V[-x].h
			: V[x].v < 0 ? V[x].l : V[x].h;
	}

	inline static int_t lo(int_t x) {
		return	x < 0 ? V[-x].v < 0 ? -V[-x].h : -V[-x].l
			: V[x].v < 0 ? V[x].h : V[x].l;
	}

	inline static uint_t var(int_t x) { return abs(V[abs(x)].v); }
	static void initopts(bool usestack = false);
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
