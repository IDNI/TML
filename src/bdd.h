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
#include <climits>
#include "defs.h"
#ifndef NOMMAP
#include "memory_map.h"
#endif

#define neg_to_odd(x) (((x)<0?(((-(x))<<1)+1):((x)<<1)))
#define hash_pair(x, y) fpairing(neg_to_odd(x), neg_to_odd(y))
#define hash_tri(x, y, z) fpairing(hash_pair(x, y), neg_to_odd(z))
#define hash_upair(x, y) fpairing(x, y)
#define hash_utri(x, y, z) fpairing(hash_upair(x, y), z)

inline size_t fpairing(size_t x, size_t y) {
	size_t z = x + y;
	z *= z+1;
	return y+(z>>1);
}

extern bool onexit;

/* The following is an implementation of attributed BDDs as defined in "Shared
 * Binary Decision Diagram with Attributed Edges for Efficient Boolean function
 * Manipulation" by Minato. The BDD reference as defined below is a
 * manifestation of the attributed edge concept and has the following bit
 * layout:
 * BDD ID: 0-31
 * SHIFT: 32-63
 * INV_INP: 31-32
 * INV_OUT: 63-64.
 * The terminal node invariants are: BDD_ID <= 1 --> SHIFT = 0 and
 * BDD_ID <= 1 --> INV_INP = 0 and BDD_ID = 0 --> INV_OUT = 0. All these ensure
 * that each attributed edge has a unique representation. */
typedef uint64_t bdd_ref;
typedef uint64_t bdd_id;
typedef uint64_t bdd_shft;
// Make a selector for the given bits of a 64-bit unsigned integer
#define MASK32(low, high) ((uint32_t(-1) >> ((low) + 32 - (high))) << (low))
#define MASK64(low, high) ((uint64_t(-1) >> ((low) + 64 - (high))) << (low))
// Extract the given bits from the given number
#define GET32(low, high, x) ((((uint32_t)(x)) & MASK32(low, high)) >> (low))
#define GET64(low, high, x) ((((uint64_t)(x)) & MASK64(low, high)) >> (low))
// Place the low bits of x into the given position
#define PLACE64(low, high, x) ((((uint64_t)(x)) << (low)) & MASK64(low, high))
// Replace the given bits of x with the low bits of y
#define REPL64(low, high, x, y) (((x) & ~MASK64(low, high)) | PLACE64(low, high, y))
// Construct a BDD reference with the given ID, shift, and inverters
#define BDD_REF(id, shift, inv_inp, inv_out) (PLACE64(0,31,id) | \
	PLACE64(32,63,(id) <= 1 ? 0 : (shift)) | PLACE64(31,32,(id) <= 1 ? 0 : (inv_inp)) | \
	PLACE64(63,64,(id) ? (inv_out) : 0))
// Get the BDD identified by this BDD reference
#define GET_BDD_ID(x) GET32(0,31,((uint32_t)(x)))
// Get the shift applied by this BDD reference
#define GET_SHIFT(x) ((bdd_shft) GET32(0,31,((uint32_t)((x) >> 32))))
// Is the input of this BDD reference inverted?
#define GET_INV_INP(x) GET32(31,32,((uint32_t)(x)))
// Is the output of this BDD reference inverted?
#define GET_INV_OUT(x) GET32(31,32,((uint32_t)((x) >> 32)))
// Set the BDD identified by this reference
#define SET_BDD_ID(y, x) (y = REPL64(0,31,y,x))
// Remove the output inverter from the BDD reference
#define BDD_ABS(x) (((uint64_t)(x)) & (uint64_t(-1) >> 1))
// Increase the shift of the BDD reference, terminal nodes cannot be shifted
#define PLUS_SHIFT(y, x) (GET_BDD_ID(y) > 1 ? REPL64(32,63,y,GET_SHIFT(y)+((int32_t)(x))) : (y))
#define INCR_SHIFT(y, x) (y = PLUS_SHIFT(y, x))
// Decrease the shift of the BDD reference, terminal nodes cannot be shifted
#define MINUS_SHIFT(y, x) (GET_BDD_ID(y) > 1 ? REPL64(32,63,y,GET_SHIFT(y)-((int32_t)(x))) : (y))
#define DECR_SHIFT(y, x) (y = MINUS_SHIFT(y, x))
// Invert supplied BDD reference, the 0 node cannot be inverted
#define FLIP_INV_OUT(x) (GET_BDD_ID(x) ? ((x) ^ (uint64_t(1) << 63)) : (x))
// Compare BDD references in such a way that output inverted ones are <0
#define BDD_LT(x, y) (((int64_t)(x)) < ((int64_t)(y)))

class bdd;
typedef std::shared_ptr<class bdd_handle> spbdd_handle;
typedef const spbdd_handle& cr_spbdd_handle;
typedef std::vector<bdd_ref> bdds;
typedef std::vector<spbdd_handle> bdd_handles;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;
#ifdef NOMMAP
typedef std::vector<class bdd> bdd_mmap;
#else
typedef std::vector<class bdd, memory_map_allocator<bdd> >bdd_mmap;
#endif

struct ite_memo {
	bdd_ref x, y, z;
	size_t hash;
	ite_memo(bdd_ref x, bdd_ref y, bdd_ref z) :
		x(x), y(y), z(z) { rehash(); }
	void rehash() {
		std::hash<bdd_ref> hsh;
		hash = hash_utri(hsh(x), hsh(y), hsh(z));
	}
	bool operator==(const ite_memo& k) const{return x==k.x&&y==k.y&&z==k.z;}
};

struct bdd_key {
	uint_t hash;
	bdd_ref h, l;
	bdd_key(){}
	bdd_key(uint_t hash, bdd_ref h, bdd_ref l) :
		hash(hash), h(h), l(l) {}
	bool operator==(const bdd_key& k) const { return h==k.h && l==k.l; }
};

template<> struct std::hash<bdd_key> {size_t operator()(const bdd_key&)const;};
template<> struct std::hash<ite_memo>{size_t operator()(const ite_memo&)const;};
template<> struct std::hash<std::array<int_t, 2>>{
	size_t operator()(const std::array<int_t, 2>&) const;
};
template<> struct std::hash<std::array<bdd_ref, 2>>{
	size_t operator()(const std::array<bdd_ref, 2>&) const;
};

const bdd_ref T = BDD_REF(1, 0, false, false), F = BDD_REF(1, 0, false, true);

spbdd_handle from_bit(uint_t b, bool v);
bool leaf(cr_spbdd_handle h);
bool trueleaf(cr_spbdd_handle h);
template <typename T>
std::basic_ostream<T>& out(std::basic_ostream<T>& os, cr_spbdd_handle x);
spbdd_handle operator&&(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle operator%(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle operator||(cr_spbdd_handle x, cr_spbdd_handle y);

spbdd_handle operator/(cr_spbdd_handle x, const bools& b);
spbdd_handle operator^(cr_spbdd_handle x, const uints& m);

spbdd_handle bdd_impl(cr_spbdd_handle x, cr_spbdd_handle y);

bool bdd_subsumes(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_shift(cr_spbdd_handle in, int_t amt);
spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y, cr_spbdd_handle z);
spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y, cr_spbdd_handle z);
spbdd_handle bdd_and_many(bdd_handles v);
spbdd_handle bdd_and_many_ex(bdd_handles v, const bools& ex);
spbdd_handle bdd_or_many(bdd_handles v);
spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools& b);
spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y, const bools&);
spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m);
spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x, cr_spbdd_handle y,
	const bools& b, const uints& m);
spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const bools& b, const uints&);
spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b, const uints& m);
spbdd_handle from_eq(uint_t x, uint_t y);
std::array<spbdd_handle, 2> solve(spbdd_handle x, uint_t v);
bdd_ref bdd_or_reduce(bdds b);
bdd_ref bdd_or_reduce(bdds b);
size_t bdd_nvars(spbdd_handle x);
size_t bdd_nvars(bdd_handles x);
vbools allsat(cr_spbdd_handle x, uint_t nvars);
extern bdd_mmap V;
extern size_t max_bdd_nodes;
#ifndef NOMMAP
extern mmap_mode bdd_mmap_mode;
#endif

// template<typename T>
// struct veccmp {
// 	bool operator()(const std::vector<T>& x, const std::vector<T>& y) const;
// };
//
// template<typename T1, typename T2>
// struct vec2cmp {
// 	typedef std::pair<std::vector<T1>, std::vector<T2>> t;
// 	bool operator()(const t& x, const t& y) const;
// };
//
// template<typename T1, typename T2, typename T3>
// struct vec3cmp {
// 	typedef std::tuple<std::vector<T1>, std::vector<T2>, std::vector<T3>> t;
// 	bool operator()(const t& x, const t& y) const;
// };
//
// // these are extern because archive needs access to them. TODO: make it better
// extern std::vector<std::unordered_map<bdd_key, int_t>> Mp, Mn;
// extern std::unordered_map<ite_memo, int_t> C;
// extern std::map<bools, std::unordered_map<std::array<int_t, 2>, int_t>,
// 	veccmp<bool>> CX;
// extern std::map<xperm, std::unordered_map<std::array<int_t,2>, int_t>,
// 	vec2cmp<bool,uint_t>> CXP;
// extern std::unordered_map<bdds, int_t> AM;
// extern std::map<bools, std::unordered_map<bdds, int_t>, veccmp<bool>> AMX;
// extern std::map<std::pair<bools,uints>, std::unordered_map<bdds,int_t>,
// 	vec2cmp<bool,uint_t>> AMXP;
// extern std::unordered_set<int_t> S;
// extern std::map<bools, std::unordered_map<int_t, int_t>, veccmp<bool>> memos_ex;
// extern std::map<uints, std::unordered_map<int_t, int_t>, veccmp<uint_t>>
// 	memos_perm;
// extern std::map<std::pair<uints, bools>, std::unordered_map<int_t, int_t>,
// 	vec2cmp<uint_t, bool>> memos_perm_ex;

void bdd_size(cr_spbdd_handle x,  std::set<uint_t>& s);
int_t bdd_root(cr_spbdd_handle x);
spbdd_handle bdd_not(cr_spbdd_handle x);
spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_or(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_xor(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_bitwise_not(cr_spbdd_handle x);
spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y);
spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, size_t bits,
		size_t n_vars);
spbdd_handle bdd_quantify(cr_spbdd_handle x, const std::vector<quant_t> &quants,
		const size_t bits, const size_t n_args);

/* A BDD is a pair of attributed references to BDDs. Separating out attributes
 * from BDDs increase the chances that BDDs can be reused in representing
 * different functions. */

class bdd {
	friend class archive;
	friend class bdd_handle;
	friend class allsat_cb;
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
	friend bdd_ref bdd_or_reduce(bdds b);
	friend spbdd_handle bdd_ite(cr_spbdd_handle x, cr_spbdd_handle y,
		cr_spbdd_handle z);
	friend spbdd_handle bdd_ite_var(uint_t x, cr_spbdd_handle y,
		cr_spbdd_handle z);
	friend spbdd_handle bdd_and_many(bdd_handles v);
	friend spbdd_handle bdd_and_many_ex(bdd_handles v, const bools& ex);
	friend spbdd_handle bdd_or_many(bdd_handles v);
	friend spbdd_handle bdd_permute_ex(cr_spbdd_handle x, const bools& b,
		const uints& m);
	friend spbdd_handle bdd_and_ex_perm(cr_spbdd_handle x, cr_spbdd_handle,
		const bools& b, const uints& m);
	friend spbdd_handle bdd_and_not_ex_perm(cr_spbdd_handle x,
		cr_spbdd_handle, const bools& b, const uints& m);
	friend spbdd_handle bdd_and_many_ex_perm(bdd_handles v, const bools& b,
		const uints&);
	friend spbdd_handle bdd_and_ex(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools& b);
	friend spbdd_handle bdd_and_not_ex(cr_spbdd_handle x, cr_spbdd_handle y,
		const bools&);
	friend std::array<spbdd_handle, 2> solve(spbdd_handle x, uint_t v);
	friend vbools allsat(cr_spbdd_handle x, uint_t nvars);
	friend spbdd_handle from_bit(uint_t b, bool v);
	friend size_t bdd_nvars(spbdd_handle x);
	friend bool leaf(cr_spbdd_handle h);
	friend bool trueleaf(cr_spbdd_handle h);
	template <typename T>
	friend std::basic_ostream<T>& out(std::basic_ostream<T>& os, cr_spbdd_handle x);
	friend void bdd_size(cr_spbdd_handle x,  std::set<uint_t>& s);
	friend int_t bdd_root(cr_spbdd_handle x);
	friend spbdd_handle bdd_not(cr_spbdd_handle x);
	friend spbdd_handle bdd_xor(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_quantify(cr_spbdd_handle x, const std::vector<quant_t> &quants,
			const size_t bits, const size_t n_args);
	friend spbdd_handle bdd_bitwise_and(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_or(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_xor(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_bitwise_not(cr_spbdd_handle x);
	friend spbdd_handle bdd_adder(cr_spbdd_handle x, cr_spbdd_handle y);
	friend spbdd_handle bdd_mult_dfs(cr_spbdd_handle x, cr_spbdd_handle y, size_t bits , size_t n_vars );
	friend spbdd_handle bdd_shift(cr_spbdd_handle x, int_t amt);
	
	/* Get the absolute BDD referenced by the given BDD reference. If the given
	 * BDD reference represents the function f, the low reference of the produced
	 * BDD represents f with the variable represented by x set to 0, and the high
	 * reference the function f with this variable set to 1. */
	
	inline static bdd get(bdd_ref x) {
		// Get the BDD that this reference is attributing
		bdd cbdd = V[GET_BDD_ID(x)];
		// Apply input inversion to the outcome
		if(GET_INV_INP(x)) std::swap(cbdd.h, cbdd.l);
		// Apply variable shifting to the outcome
		INCR_SHIFT(cbdd.l, GET_SHIFT(x));
		INCR_SHIFT(cbdd.h, GET_SHIFT(x));
		// Apply output inversion to the outcome
		if(GET_INV_OUT(x)) { cbdd.l = FLIP_INV_OUT(cbdd.l); cbdd.h = FLIP_INV_OUT(cbdd.h); }
		return cbdd;
	}

	static bdd_ref bdd_and(bdd_ref x, bdd_ref y);
	static bdd_ref bdd_and_ex(bdd_ref x, bdd_ref y, const bools& ex);
	static bdd_ref bdd_and_ex(bdd_ref x, bdd_ref y, const bools& ex,
		std::unordered_map<std::array<bdd_ref, 2>, bdd_ref>& memo,
		std::unordered_map<bdd_ref, bdd_ref>& memo2, bdd_shft last);
	static bdd_ref bdd_or(bdd_ref x, bdd_ref y) {
		const bdd_ref and_ref = bdd_and(FLIP_INV_OUT(x), FLIP_INV_OUT(y));
		// Apply output inversion to constant expression to avoid repeat calls to
		// bdd_and
		return FLIP_INV_OUT(and_ref);
	}
	static bdd_ref bdd_ite(bdd_ref x, bdd_ref y, bdd_ref z);
	static bdd_ref bdd_ite_var(uint_t x, bdd_ref y, bdd_ref z);
	static bdd_ref bdd_and_many(bdds v);
	static bdd_ref bdd_and_many_ex(bdds v, const bools& ex);
	static bdd_ref bdd_ex(bdd_ref x, const bools& b,
		std::unordered_map<bdd_ref, bdd_ref>& memo, uint_t last);
	static bdd_ref bdd_ex(bdd_ref x, const bools& b);
	static bdd_ref bdd_permute(bdd_ref x, const uints& m,
		std::unordered_map<bdd_ref, bdd_ref>& memo);
	static bdd_ref bdd_permute_ex(bdd_ref x, const bools& b, const uints& m,
		size_t last, std::unordered_map<bdd_ref, bdd_ref>& memo);
	static bdd_ref bdd_permute_ex(bdd_ref x, const bools& b, const uints& m);
	static bool solve(bdd_ref x, uint_t v, bdd_ref& l, bdd_ref& h);
	static void mark_all(bdd_ref i);
	static size_t bdd_and_many_iter(bdds, bdds&, bdds&, bdd_ref&, size_t&);
	static char bdd_and_many_ex_iter(const bdds&v, bdds& h, bdds& l,
		bdd_shft &m);
	static bdd_ref bdd_and_ex_perm(bdd_ref x, bdd_ref y, const bools& ex,
		const uints&);
	static bdd_ref bdd_and_many_ex_perm(bdds v, const bools&, const uints&);
	static void sat(uint_t v, uint_t nvars, bdd_ref t, bools& p, vbools& r);
	static vbools allsat(bdd_ref x, uint_t nvars);
	static void bdd_sz(bdd_ref x, std::set<bdd_ref>& s);
	static void bdd_nvars(bdd_ref x, std::set<int_t>& s);
	static size_t bdd_nvars(bdd_ref x);
	static bool bdd_subsumes(bdd_ref x, bdd_ref y);
	static bdd_ref add(uint_t v, bdd_ref h, bdd_ref l);
	inline static bdd_ref from_bit(uint_t b, bool v);
	inline static void max_bdd_size_check();
	inline static bool leaf(bdd_ref t) { return BDD_ABS(t) == T; }
	inline static bool trueleaf(bdd_ref t) { return !GET_INV_OUT(t); }
	template <typename T>
	static std::basic_ostream<T>& out(std::basic_ostream<T>& os, bdd_ref x);
	bdd_ref h, l;

	//---
	static void bdd_sz_abs(bdd_ref x, std::set<uint_t>& s);
	static bdd_ref bdd_xor(bdd_ref x, bdd_ref y);
	static bdd_ref bdd_quantify(bdd_ref x, uint_t bit, const std::vector<quant_t> &quants,
			const size_t bits, const size_t n_args);
	static bdd_ref bitwise_and(bdd_ref a_in, bdd_ref b_in);
	static bdd_ref bitwise_or(bdd_ref a_in, bdd_ref b_in);
	static bdd_ref bitwise_xor(bdd_ref a_in, bdd_ref b_in);
	static bdd_ref bitwise_not(bdd_ref a_in);
	static bdd_ref adder(bdd_ref a_in, bdd_ref b_in, bool carry, size_t bit);
	typedef enum { L, H, X, U } t_path;
	typedef std::vector<t_path> t_pathv;
	static bool bdd_next_path(std::vector<bdd_ref> &a, int_t &i, int_t &bit, t_pathv &path,
			size_t bits, size_t n_args);
	static int_t balance_paths(t_pathv & next_path_a, t_pathv & next_path_b, size_t bits,
			std::vector<t_pathv> &aux_path_a, std::vector<t_pathv> &aux_path_b);
	static bdd_ref solve_path(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static bdd_ref solve_pathXL(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static bdd_ref solve_pathLX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static bdd_ref solve_pathXH(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static bdd_ref solve_pathHX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static bdd_ref solve_pathXX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static bdd_ref merge_pathX(size_t i, size_t bits, bool carry, size_t n_args, size_t depth,
			t_pathv &path_a, t_pathv &path_b, t_pathv &pathX_a, t_pathv &pathX_b);
	static void satcount_arith(bdd_ref a_in, size_t bit, size_t bits, size_t factor, size_t n_args, size_t &count);
	static bdd_ref zero(size_t arg, size_t bits, size_t n_args);
	static bool is_zero(bdd_ref a_in, size_t bits);
	static void adder_be(bdd_ref a_in, bdd_ref b_in, size_t bits, size_t depth,
			size_t n_args, bdd_ref &c);
	static bdd_ref adder_accs(bdd_ref b_in, bdd_ref accs, size_t depth, size_t bits, size_t n_args);
	static void mult_dfs(bdd_ref a_in, bdd_ref b_in, bdd_ref *accs, size_t depth, size_t bits,
			size_t n_args, bdd_ref &c) ;
	static bdd_ref bdd_shift(bdd_ref a_in, int_t amt);
	static bdd_ref copy_arg2arg(bdd_ref a , size_t arg_a, size_t arg_b, size_t bits, size_t n_args);
	static bdd_ref shr(bdd_ref a_in, size_t arg, size_t bits, size_t n_args);
	static bdd_ref shlx(bdd_ref b_in, size_t x, size_t bits, size_t n_args);

public:
	bdd(bdd_ref h, bdd_ref l);
	inline bool operator==(const bdd& b) const {
		return h == b.h && l == b.l;
	}
#ifndef NOMMAP
	static void init(mmap_mode m = MMAP_NONE, size_t max_size=10000,
		const std::string fn="");
#else
	static void init();
#endif
	static void gc();
	template <typename T>
	static std::basic_ostream<T>& stats(std::basic_ostream<T>& os);
	static size_t get_ite_cache_size();
	static void set_gc_limit(size_t new_gc_limit);
	static void set_gc_enabled(bool new_gc_enabled);
	
	/* Return the absolute BDD corresponding to the high part of the given BDD
	 * reference. If x represents a boolean function f, then this function returns
	 * a reference to a BDD representing the function f with the variable
	 * corresponding to x set to 1. */
	
	inline static bdd_ref hi(bdd_ref x) {
		// Get the BDD that this reference is attributing
		bdd &cbdd = V[GET_BDD_ID(x)];
		// Apply output inversion
		return GET_INV_OUT(x) ? FLIP_INV_OUT(PLUS_SHIFT(GET_INV_INP(x) ? cbdd.l : cbdd.h, GET_SHIFT(x))) : PLUS_SHIFT(GET_INV_INP(x) ? cbdd.l : cbdd.h, GET_SHIFT(x));
	}
	
	/* Definition is analogous to hi with high and 1 replaced by low and 0. */

	inline static bdd_ref lo(bdd_ref x) {
		// Get the BDD that this reference is attributing
		bdd &cbdd = V[GET_BDD_ID(x)];
		// Apply input inversion
		// Apply output inversion
		return GET_INV_OUT(x) ? FLIP_INV_OUT(PLUS_SHIFT(GET_INV_INP(x) ? cbdd.h : cbdd.l, GET_SHIFT(x))) : PLUS_SHIFT(GET_INV_INP(x) ? cbdd.h : cbdd.l, GET_SHIFT(x));
	}
	
	/* The variable of a BDD reference is its root/absolute shift. */

	inline static bdd_shft var(bdd_ref x) { return GET_SHIFT(x); }

	static size_t satcount_perm(bdd_ref x, bdd_shft leafvar);

	static bdd_shft getvar(bdd_ref x);
	static size_t satcount_k(bdd_ref x, const bools& ex, const uints& perm);
	static size_t satcount_k(bdd_ref x, bdd_shft leafvar,
		std::map<bdd_shft, bdd_shft>& mapvars);
	static size_t satcount(spbdd_handle x, const bools& inv);
};

class bdd_handle {
	friend class bdd;
	friend class archive;
	bdd_handle(bdd_ref b) : b(b) { }//bdd::mark(b); }
	static void update(const std::vector<int_t>& p);
	static std::unordered_map<bdd_ref, std::weak_ptr<bdd_handle>> M;
public:
	bdd_ref b;
	static spbdd_handle get(bdd_ref b);
	static spbdd_handle T, F;
	~bdd_handle() {
		if (onexit) return;
		//if (abs(b) > 1 && (M.erase(b), !has(M, -b))) bdd::unmark(b);
		if (GET_BDD_ID(b) > 1) M.erase(b);//, !has(M, -b))) bdd::unmark(b);
	}
};

class allsat_cb {
public:
	typedef std::function<void(const bools&, bdd_ref)> callback;
	allsat_cb(cr_spbdd_handle r, uint_t nvars, callback f) :
		r(r->b), nvars(nvars), f(f), p(nvars) {}
	void operator()() { sat(r); }
private:
	bdd_ref r;
	const uint_t nvars;
	uint_t v = 1;
	callback f;
	bools p;
	void sat(bdd_ref x);
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
	bdd_ref r;
	const uint_t nvars;
	uint_t v = 1;
	bools p;
	const bools& inv;
	std::set<bools> vp;
	void sat(bdd_ref x);
};
