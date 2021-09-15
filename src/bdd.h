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
#ifndef NOMMAP
#include "memory_map.h"
#endif

#define neg_to_odd(x) (((x)<0?(((-(x))<<1)+1):((x)<<1)))
#define hash_pair(x, y) fpairing(neg_to_odd(x), neg_to_odd(y))
#define hash_tri(x, y, z) fpairing(hash_pair(x, y), neg_to_odd(z))

inline size_t fpairing(size_t x, size_t y) {
	size_t z = x + y;
	z *= z+1;
	return y+(z>>1);
}

extern bool onexit;

class bdd_ref {
	public:
		int_t bdd_id, shift;
		bdd_ref(int_t bdd_id = 0, int_t shift = 0) : bdd_id(bdd_id), shift(shift) {}
		bool operator==(const bdd_ref &b) const { return bdd_id == b.bdd_id; }
		bool operator<(const bdd_ref &b) const { return bdd_id < b.bdd_id; }
		bool operator>(const bdd_ref &b) const { return bdd_id > b.bdd_id; }
		bool operator!=(const bdd_ref &b) const { return bdd_id != b.bdd_id; }
		bdd_ref operator-() const { return bdd_ref(-bdd_id, shift); }
		int_t sgn() const { return (bdd_id > 0) - (bdd_id < 0); }
		bdd_ref abs() const { return bdd_ref(std::abs(bdd_id), shift); }
		// Gives each distinct reference a distinct fingerprint such that a
		// reference for a negated BDDs has the opposite sign.
		int_t sfgpt() const { return bdd_id; }
		// Gives each distinct reference a distinct unsigned fingerprint
		size_t ufgpt() const { return (std::abs(bdd_id) << 1) + (bdd_id < 0); }
		bdd_ref shift_var(int delta) const { return bdd_ref(bdd_id, shift + delta); }
};

template<> struct std::hash<bdd_ref> {
	std::size_t operator()(const bdd_ref &br) const {
		return br.ufgpt();
	}
};

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
		x(x), y(y), z(z), hash(hash_tri(x.sfgpt(), y.sfgpt(), z.sfgpt())) {}
	void rehash() { hash = hash_tri(x.sfgpt(), y.sfgpt(), z.sfgpt()); }
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

const bdd_ref T(1), F(-1);

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
std::array<spbdd_handle, 2> solve(spbdd_handle x, int_t v);
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

void bdd_size(cr_spbdd_handle x,  std::set<int_t>& s);
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
	friend std::array<spbdd_handle, 2> solve(spbdd_handle x, int_t v);
	friend vbools allsat(cr_spbdd_handle x, uint_t nvars);
	friend spbdd_handle from_bit(uint_t b, bool v);
	friend size_t bdd_nvars(spbdd_handle x);
	friend bool leaf(cr_spbdd_handle h);
	friend bool trueleaf(cr_spbdd_handle h);
	template <typename T>
	friend std::basic_ostream<T>& out(std::basic_ostream<T>& os, cr_spbdd_handle x);
	friend void bdd_size(cr_spbdd_handle x,  std::set<bdd_ref>& s);
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

	/*inline static bdd get(bdd_ref x) {
		if (x.sfgpt() > 0) {
			const bdd &y = V[x.sfgpt()];
			return x.shift > 0 ? y : bdd(-y.v, y.l, y.h);
		} else {
			const bdd &y = V[-x.sfgpt()];
			return x.shift > 0 ? bdd(y.v, -y.h, -y.l) : bdd(-y.v, -y.l, -y.h);
		}
	}*/

	static bdd_ref bdd_and(bdd_ref x, bdd_ref y);
	static bdd_ref bdd_and_ex(bdd_ref x, bdd_ref y, const bools& ex);
	static bdd_ref bdd_and_ex(bdd_ref x, bdd_ref y, const bools& ex,
		std::unordered_map<std::array<bdd_ref, 2>, bdd_ref>& memo,
		std::unordered_map<bdd_ref, bdd_ref>& memo2, int_t last);
	static bdd_ref bdd_or(bdd_ref x, bdd_ref y) { return -bdd_and(-x, -y); }
	static bdd_ref bdd_ite(bdd_ref x, bdd_ref y, bdd_ref z);
	static bdd_ref bdd_ite_var(uint_t x, bdd_ref y, bdd_ref z);
	static bdd_ref bdd_and_many(bdds v);
	static bdd_ref bdd_and_many_ex(bdds v, const bools& ex);
	static bdd_ref bdd_and_many_ex(bdds v, const bools& ex,
		std::unordered_map<bdds, int_t>& memo,
		std::unordered_map<int_t, int_t>& m2,
		std::unordered_map<std::array<int_t, 2>, int_t>& m3);
	static bdd_ref bdd_ex(bdd_ref x, const bools& b,
		std::unordered_map<bdd_ref, bdd_ref>& memo, int_t last);
	static bdd_ref bdd_ex(bdd_ref x, const bools& b);
	static bdd_ref bdd_permute(const bdd_ref &x, const uints& m,
		std::unordered_map<bdd_ref, bdd_ref>& memo);
	static bdd_ref bdd_permute_ex(bdd_ref x, const bools& b, const uints& m,
		size_t last, std::unordered_map<bdd_ref, bdd_ref>& memo);
	static bdd_ref bdd_permute_ex(bdd_ref x, const bools& b, const uints& m);
	static bool solve(bdd_ref x, int_t v, bdd_ref& l, bdd_ref& h);
	static void mark_all(bdd_ref i);
	static size_t bdd_and_many_iter(bdds, bdds&, bdds&, bdd_ref&, size_t&);
	static char bdd_and_many_ex_iter(const bdds&v, bdds& h, bdds& l,
		int_t &m);
	static bdd_ref bdd_and_ex_perm(bdd_ref x, bdd_ref y, const bools& ex,
		const uints&);
	static bdd_ref bdd_and_many_ex_perm(bdds v, const bools&, const uints&);
	static void sat(uint_t v, uint_t nvars, bdd_ref t, bools& p, vbools& r);
	static vbools allsat(bdd_ref x, uint_t nvars);
	static bool am_simplify(bdds& v,const std::unordered_map<bdds, bdd_ref>&);
	static void bdd_sz(bdd_ref x, std::set<bdd_ref>& s);
	static void bdd_nvars(bdd_ref x, std::set<int_t>& s);
	static size_t bdd_nvars(bdd_ref x);
	static bool bdd_subsumes(bdd_ref x, bdd_ref y);
	static bdd_ref add(int_t v, bdd_ref h, bdd_ref l);
	inline static bdd_ref from_bit(uint_t b, bool v);
	inline static void max_bdd_size_check();
	inline static bool leaf(bdd_ref t) { return t.abs() == T; }
	inline static bool trueleaf(bdd_ref t) { return t.sfgpt() > 0; }
	template <typename T>
	static std::basic_ostream<T>& out(std::basic_ostream<T>& os, bdd_ref x);
	bdd_ref h, l;
	//int_t v;

	//---
	static void bdd_sz_abs(bdd_ref x, std::set<bdd_ref>& s);
	static bdd_ref bdd_xor(bdd_ref x, bdd_ref y);
	static bdd_ref bdd_quantify(bdd_ref x, int_t bit, const std::vector<quant_t> &quants,
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
	static bdd_ref copy(bdd_ref a_in);
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
		const std::string fn="", bool gc = true);
#else
	static void init(bool gc = true);
#endif
	static void gc();
	template <typename T>
	static std::basic_ostream<T>& stats(std::basic_ostream<T>& os);
	inline static bdd_ref hi(bdd_ref x) {
		bdd &cbdd = V[x.abs().sfgpt()];
		bdd_ref nbdd = cbdd.h.shift_var(x.shift);
		return x.sgn() > 0 ? nbdd : -nbdd;
	}

	inline static bdd_ref lo(bdd_ref x) {
		bdd &cbdd = V[x.abs().sfgpt()];
		bdd_ref nbdd = cbdd.l.shift_var(x.shift);
		return x.sgn() > 0 ? nbdd : -nbdd;
	}

	inline static uint_t var(bdd_ref x) { return abs(x.shift); }

	static size_t satcount_perm(bdd_ref x, size_t leafvar);

	static size_t getvar(bdd_ref h, bdd_ref l, int_t v, bdd_ref x, size_t maxv);
	static size_t satcount_k(bdd_ref x, const bools& ex, const uints& perm);
	static size_t satcount_k(bdd_ref x, size_t leafvar,
		std::map<int_t, int_t>& mapvars);
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
		if (b.abs().sfgpt() > 1) M.erase(b);//, !has(M, -b))) bdd::unmark(b);
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
