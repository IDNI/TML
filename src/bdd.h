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
#ifndef __BDD_H__
#define __BDD_H__

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

extern bool onexit;

class bdd;
typedef std::shared_ptr<class bdd_handle> spbdd_handle;
typedef const spbdd_handle& cr_spbdd_handle;
typedef std::vector<int_t> bdds;
typedef std::vector<spbdd_handle> bdd_handles;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;

typedef std::pair<bools, uints> xperm;
typedef std::tuple<bools, uints, uints> xperm_bits;
typedef std::tuple<uints, bools, uints> permex_bits;

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
template<> struct std::hash<uints> { 
	size_t operator()(const uints& v) const {
		size_t r = 0;
		for (auto i : v) r ^= i;
		return r;
	}
};
template<> struct std::hash<xperm> {
	size_t operator()(const xperm&) const;
};

const int_t T = 1, F = -1;

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
spbdd_handle bdd_or_many(bdd_handles v);
spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools& b);
spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools&);
//spbdd_handle bdd_and_ex_perm(
//	cr_spbdd_handle x, cr_spbdd_handle y, const bools& b, const uints& m);
spbdd_handle bdd_and_ex_perm(
	cr_spbdd_handle, cr_spbdd_handle, const bools&, const uints&, const uints&);
//spbdd_handle bdd_and_not_ex_perm(
//	cr_spbdd_handle x, cr_spbdd_handle y, const bools& b, const uints& m);
spbdd_handle bdd_and_not_ex_perm(
	cr_spbdd_handle, cr_spbdd_handle, const bools&, const uints&, const uints&);
//spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const bools& b, const uints&);
spbdd_handle bdd_and_many_ex_perm(
	bdd_handles v, const bools& b, const uints&, const uints&);
spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const xperm_bits&);
//spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const uints& m);
spbdd_handle bdd_permute_ex(
	cr_spbdd_handle x, const bools& ex, const uints& perm, const uints& vbits);

spbdd_handle from_eq(uint_t x, uint_t y);
std::array<spbdd_handle, 2> solve(spbdd_handle x, int_t v);
int_t bdd_or_reduce(bdds b);
int_t bdd_or_reduce(bdds b);
size_t bdd_nvars(spbdd_handle x);
size_t bdd_nvars(bdd_handles x);
vbools allsat(cr_spbdd_handle x, uint_t nvars);
extern std::vector<class bdd> V;

void bdd_size(cr_spbdd_handle x,  std::set<int_t>& s);
int_t bdd_root(cr_spbdd_handle x);
spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_or(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_xor(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_not(cr_spbdd_handle x);
spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, size_t bits, size_t n_vars);

class bdd {
	friend class bdd_handle;
	template<typename _Predicate> friend class allsat_cb;
	friend class satcount_iter;
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
	friend spbdd_handle bdd_or_many(bdd_handles v);
	//friend spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b,
	//	const uints& m);
	friend spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& ex,
		const uints& perm, const uints& vbits);
	friend spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle,
		const bools& ex, const uints& perm, const uints& vbits);
	friend spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools& ex, const uints& p, const uints& vbits);
	//friend spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x,
	//	cr_spbdd_handle, const bools& b, const uints& m);
	friend spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle, cr_spbdd_handle,
		const bools&, const uints&, const uints&);
	friend spbdd_handle bdd_and_many_ex_perm(
		bdd_handles v, const bools& b, const uints&, const uints&);
	friend spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools& b);
	friend spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools&);
	friend std::array<spbdd_handle, 2> solve(spbdd_handle x, int_t v);
	friend vbools allsat(cr_spbdd_handle x, uint_t nvars);
	friend spbdd_handle from_bit(uint_t b, bool v);
	friend size_t bdd_nvars(spbdd_handle x);
	friend bool leaf(cr_spbdd_handle h);
	friend bool trueleaf(cr_spbdd_handle h);
	friend std::wostream& out(std::wostream& os, cr_spbdd_handle x);
	friend std::ostream& write_bdd(std::ostream& os);
	friend std::istream& read_bdd(std::istream& is);

	friend void bdd_size(cr_spbdd_handle x,  std::set<int_t>& s);
	friend int_t bdd_root(cr_spbdd_handle x);
	friend spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_or(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_xor(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_not(cr_spbdd_handle x);
	friend spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, size_t bits , size_t n_vars );

	inline static bdd get(int_t x) {
		if (x > 0) {
			const bdd &y = V[x];
			return y.v > 0 ? y : bdd(-y.v, y.l, y.h);
		}
		const bdd &y = V[-x];
		return y.v > 0 ? bdd(y.v, -y.h, -y.l) : bdd(-y.v, -y.l, -y.h);
	}

	static int_t bdd_and(int_t x, int_t y);
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
	//static int_t bdd_permute_ex(int_t x, const bools& b, const uints& m,
	//	size_t last, std::unordered_map<int_t, int_t>& memo);
	//static int_t bdd_permute_ex(int_t x, const bools& b, const uints& m);
	static int_t bdd_permute_ex(int_t x, const bools& ex, const uints& perm, 
		const uints& vbits, size_t last, std::unordered_map<int_t, int_t>& m);
	static int_t bdd_permute_ex(
		int_t x, const bools& ex, const uints& perm, const uints& vbits);

	static bool solve(int_t x, int_t v, int_t& l, int_t& h);
	static void mark_all(int_t i);
	static size_t bdd_and_many_iter(bdds, bdds&, bdds&, int_t&, size_t&);
	static char bdd_and_many_ex_iter(const bdds&v, bdds& h, bdds& l,
		int_t &m);
	//static int_t bdd_and_ex_perm(
	//	int_t x, int_t y, const bools& ex, const uints&);
	static int_t bdd_and_ex_perm(
		int_t x, int_t y, const bools& ex, const uints& p, const uints& vbits);
	//static int_t bdd_and_many_ex_perm(bdds v, const bools&, const uints&);
	static int_t bdd_and_many_ex_perm(
		bdds v, const bools&, const uints&, const uints&);
	static void sat(uint_t v, uint_t nvars, int_t t, bools& p, vbools& r);
	static vbools allsat(int_t x, uint_t nvars);
	static bool am_simplify(bdds& v,const std::unordered_map<bdds, int_t>&);
	static void bdd_sz(int_t x, std::set<int_t>& s);
	static void bdd_nvars(int_t x, std::set<int_t>& s);
	static size_t bdd_nvars(int_t x);
	static bool bdd_subsumes(int_t x, int_t y);
	static int_t add(int_t v, int_t h, int_t l);
	static int_t from_bit(uint_t b, bool v);
	inline static bool leaf(int_t t) { return abs(t) == T; }
	inline static bool trueleaf(int_t t) { return t > 0; }
	static std::wostream& out(std::wostream& os, int_t x);
	int_t h, l, v;

	//XXX: work-in-progress
	static void bdd_sz_abs(int_t x, std::set<int_t>& s);
	static int_t bdd_xor(int_t x, int_t y);

	static int_t bitwiseAND(int_t a_in, int_t b_in);
	static int_t bitwiseOR(int_t a_in, int_t b_in);
	static int_t bitwiseXOR(int_t a_in, int_t b_in);
	static int_t bitwiseNOT(int_t a_in);

	static int_t ADDER(int_t a_in, int_t b_in, bool carry, size_t bit);

	typedef enum { L, H, X, U } t_path;
	typedef std::vector<t_path> t_pathv;

	static bool bdd_next_path(std::vector<bdd> &a, int_t &i, int_t &bit, t_pathv &path,
			size_t bits, size_t n_args);
	static int_t balance_paths(t_pathv & next_path_a, t_pathv & next_path_b, size_t bits,
			std::vector<t_pathv> &aux_path_a, std::vector<t_pathv> &aux_path_b);
	static int_t solve_path(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static int_t solve_pathXL(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static int_t solve_pathLX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static int_t solve_pathXH(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static int_t solve_pathHX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static int_t solve_pathXX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static int_t merge_pathX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);

	static void satcount_arith(bdd a_in, size_t bit, size_t bits, size_t factor, size_t n_args, size_t &count);
	static int_t zero(size_t arg, size_t bits, size_t n_args);
	static bool is_zero(int_t a_in, size_t bits);

	static void ADDER_BE(int_t a_in, int_t b_in, size_t bits, size_t depth,
			size_t n_args, int_t &c);
	static int_t ADDER_ACCS(int_t b_in, int_t accs, size_t depth, size_t bits, size_t n_args);
	static void MULT_DFS(int_t a_in, int_t b_in, int_t *accs, size_t depth, size_t bits,
			size_t n_args, int_t &c) ;

	static int_t COPY(int_t a_in);
	static int_t COPY_ARG2ARG(int_t a , size_t arg_a, size_t arg_b, size_t bits, size_t n_args);
	static int_t SHR(int_t a_in, size_t arg, size_t bits, size_t n_args);
	static int_t SHLx(int_t b_in, size_t x, size_t bits, size_t n_args);

public:
	bdd(int_t v, int_t h, int_t l);
	inline bool operator==(const bdd& b) const {
		return v == b.v && h == b.h && l == b.l;
	}
	static void init();
	static void gc();
	static void cleancache();
	static void init_cache();
	static std::wostream& stats(std::wostream& os);
	inline static int_t hi(int_t x) {
		return	x < 0 ? V[-x].v < 0 ? -V[-x].l : -V[-x].h
			: V[x].v < 0 ? V[x].l : V[x].h;
	}

	inline static int_t lo(int_t x) {
		return	x < 0 ? V[-x].v < 0 ? -V[-x].h : -V[-x].l
			: V[x].v < 0 ? V[x].h : V[x].l;
	}

	inline static uint_t var(int_t x) { return abs(V[abs(x)].v); }

	static size_t satcount_perm(int_t x, size_t leafvar);
	static size_t satcount_perm(const bdd& bx, int_t x, size_t leafvar);

	static size_t getvar(int_t h, int_t l, int_t v, int_t x, size_t maxv);
	static size_t satcount_k(int_t x, const bools& ex, const uints& perm);
	static size_t satcount_k(const bdd& bx, int_t x, size_t leafvar,
		std::map<int_t, int_t>& mapvars);
	static size_t satcount(spbdd_handle x, const bools& inv);
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
		if (onexit) return;
		//if (abs(b) > 1 && (M.erase(b), !has(M, -b))) bdd::unmark(b);
		if (abs(b) > 1) M.erase(b);//, !has(M, -b))) bdd::unmark(b);
	}
};

template<typename _Predicate>
class allsat_cb {
public:
	allsat_cb(cr_spbdd_handle r, uint_t nvars, _Predicate&& f) :
		r(r->b), nvars(nvars), f(f), p(nvars) {}
	void operator()() { sat(r); }
private:
	int_t r;
	const uint_t nvars;
	uint_t v = 1;
	_Predicate f;
	bools p;
	void sat(int_t x) {
		if (x == F) return;
		const bdd bx = bdd::get(x);
		if (!bdd::leaf(x) && v < bdd::var(x)) {
			if (bdd::var(x) > nvars) {
				//return;
			}
			DBG(assert(bdd::var(x) <= nvars);)
			p[++v-2] = true, sat(x), p[v-2] = false, sat(x), --v;
		} else if (v != nvars + 1)
			p[++v-2] = true, sat(bx.h),
			p[v-2] = false, sat(bx.l), --v;
		else f(p, x);
	}
};

class satcount_iter {
public:
	satcount_iter(cr_spbdd_handle r, uint_t nvars, const bools& inv) :
		r(r->b), nvars(nvars), p(nvars), inv(inv), vp() {}
	size_t count() { 
		sat(r);
		return vp.size();
	}
private:
	int_t r;
	const uint_t nvars;
	uint_t v = 1;
	bools p;
	const bools& inv;
	std::set<bools> vp;
	void sat(int_t x);
};
#endif // __BDD_H__
