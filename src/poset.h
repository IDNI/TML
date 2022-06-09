#ifndef TML_POSET_H
#define TML_POSET_H

#include <unordered_map>
#include <vector>
#include <memory>
#include <functional>
#include "defs.h"

class PersistentUnionFind;
struct PersistentSet;
struct PersistentPairs;
class poset;

extern std::vector<poset> P;
extern std::vector<poset> NP;

template<>
struct std::hash<PersistentUnionFind> {
	size_t operator()(const PersistentUnionFind &) const;
};

template<>
struct std::hash<PersistentSet> {
	size_t operator()(const PersistentSet &) const;
};

template<>
struct std::hash<PersistentPairs> {
	size_t operator()(const PersistentPairs &) const;
};

template<>
struct std::hash<poset> {
	size_t operator()(const poset &) const;
};

template<>
struct std::hash<std::pair<int_t, int_t>> {
	size_t operator()(const std::pair<int_t, int_t> &) const;
};

template<>
struct std::hash<std::pair<int_t, std::pair<int_t, int_t>>> {
	size_t
	operator()(const std::pair<int_t, std::pair<int_t, int_t>> &) const;
};

class PersistentArray {
	typedef PersistentArray p_arr;
	typedef std::shared_ptr<PersistentArray> sppa;
	typedef std::vector<int_t> storage;

	int_t p = -1, v = -1;
	sppa diff;
  public:
	PersistentArray() : diff(nullptr) {}

	PersistentArray(int_t pos, int_t val, sppa &a) : p(pos), v(val),
							 diff(a) {}

	friend class PersistentUnionFind;

	static sppa
	init(storage &arr, int_t n, std::function<int_t(int_t)> &&f) {
		if (!arr.empty()) return nullptr;
		arr.reserve(n);
		for (int_t i = 0; i < n; ++i) arr.emplace_back(f(i));
		return std::make_shared<p_arr>(PersistentArray());
	}

	static void
	resize(storage &arr, int_t n, std::function<int_t(int_t)> &&f) {
		arr.reserve(n);
		for (int_t i = arr.size(); i < n; ++i) arr.emplace_back(f(i));
	}

	static int_t get(storage &arr, const sppa &t, int_t pos);
	static sppa set(storage &arr, const sppa &t, int_t pos, int_t val);
	static void undo(storage &arr, const sppa &current, const sppa &last);
	static void reroot(storage &arr, const sppa &t);

	static int_t size(storage &arr) { return (int_t) arr.size(); }
};

class PersistentUnionFind {
	typedef PersistentUnionFind puf;
	typedef PersistentArray p_arr;
	typedef std::shared_ptr<PersistentArray> sppa;

	static std::vector<int_t> parent_s;
	static std::vector<int_t> link_s;
	static std::vector<int_t> hashes_s;
	mutable sppa arr_pt;
	sppa link_pt;
	sppa hash_pt;
	int_t hash = 0;

	explicit PersistentUnionFind(int_t n) {
		arr_pt = p_arr::init(parent_s, n, [](int_t i) { return i; });
		link_pt = p_arr::init(link_s, n, [](int_t i) { return i; });
		hash_pt = p_arr::init(hashes_s, n, [](int_t i) { return 0; });
	}

	// Create puf taking the change from setting value at position x to y into account
	explicit PersistentUnionFind(sppa &&a_ptr, sppa &&l_ptr, sppa &&h_ptr,
				     int_t h_old, int_t x, int_t y,
				     int_t hash_x, int_t hash_y) {
		arr_pt = move(a_ptr), link_pt = move(l_ptr), hash_pt = move(
			h_ptr);
		hash = h_old ^ hash_x ^ hash_y ^ hash_set(x, y, hash_x, hash_y);
	}

	static int_t add(puf &uf);
	static int_t update(const puf &t, int_t x, int_t y);
	static void split_set (std::vector<int_t> &s, puf& uf, int_t root);
	static void split_linking(std::vector<int_t> &s, sppa& link_p,
				  int_t root);
	static void
	extend_eq_set(std::vector<std::pair<int_t, int_t>> &diffs, int_t root,
		      puf& uf, std::vector<int_t> &eq_set);
	static sppa update_link(const puf &t, int_t x, int_t y);
	static int_t find(const puf &t, int_t elem);
	static std::vector<int_t> get_equal(const puf& uf, int_t x);
  public:
	PersistentUnionFind() = delete;
	bool operator==(const puf &) const;
	friend std::hash<puf>;

	static void init(int_t n);
	static int_t find(int_t t, int_t elem);
	static int_t merge(int_t t, int_t x, int_t y);
	static int_t intersect(int_t t1, int_t t2);
	static bool equal(int_t t, int_t x, int_t y);
	static std::vector<int_t> get_equal(int_t t, int_t x);
	static int_t rm_equal(int_t t, int_t x);
	static bool resize(int_t n);
	static int_t size();

	//Hash root representatives of two sets
	inline static int_t
	hash_set(int_t x, int_t y, int_t x_hash, int_t y_hash) {
		// A singleton set still has hash 0
		// Singleton sets are hashed to their square
		return ((x_hash == 0 ? x * x : x_hash) +
			(y_hash == 0 ? y * y : y_hash));
	}

	template<typename T>
	static std::basic_ostream<T> print(int_t uf, std::basic_ostream<T> &os);
};

// The representative of a set of ints is its smallest element
struct PersistentSet {
	// Element in set
	// If e is 0 we are dealing with the empty set
	int_t e;
	// Pointer to next element
	// If n is 0 we have reached the end of a set
	int_t n;
	PersistentSet() = delete;

	PersistentSet(int_t e_, int_t n_) : e(e_), n(n_) {}

	bool operator==(const PersistentSet &) const;
	static int_t add(int_t e, int_t n);
	static void init();
	// The insertion will return 0, if the insertion causes a contradiction
	static int_t insert(int_t set_id, int_t elem);
	static int_t remove(int_t set_id, int_t elem);
	static bool empty(int_t set_id);
	static bool contains(int_t set_id, int_t elem);
	static int_t find(int_t set_id, int_t elem);
	static int_t next(int_t set_id);
	static PersistentSet get(int_t set_id);
	static void print(int_t set_id);
};

// The representative of a set of pairs is its smallest element
struct PersistentPairs {
	// Element in set
	// If e is 0 we are dealing with the empty set
	std::pair<int_t, int_t> e;
	// Pointer to next element
	// If n is 0 we have reached the end of a set
	int_t n;
	PersistentPairs() = delete;

	PersistentPairs(std::pair<int_t, int_t> &&e_, int_t n_) : e(e_),
								  n(n_) {}

	bool operator==(const PersistentPairs &) const;
	static std::pair<int_t, int_t> form(std::pair<int_t, int_t> &);
	static int_t add(std::pair<int_t, int_t> &e, int_t n);
	static void init();
	static int_t insert(int_t set_id, std::pair<int_t, int_t> &elem);
	static int_t insert(int_t set_id, int_t fst, int_t snd);
	static int_t remove(int_t set_id, std::pair<int_t, int_t> &elem);
	static bool empty(int_t set_id);
	static bool contains(int_t set_id, std::pair<int_t, int_t> &elem);
	static std::vector<int_t> implies(int_t set_id, int_t elem);
	static int_t next(int_t set_id);
	static PersistentPairs get(int_t set_id);
	static void print(int_t set_id);
};

/*
 * A poset contains the 2-CNF part of a BDD.
 * The storage is divided into three persistent data structures.
 * UnionFind for the equal variables, Pairs for the implications and Sets for
 * single variables being True or False.
 */
class poset {
	using pu = PersistentUnionFind;
	using pp = PersistentPairs;
	using ps = PersistentSet;
	// Equal variables, represented by a pointer to the uf_univ
	int_t eqs = 0;
	// Implications, represented by a pointer to the pair_univ
	int_t imps = 0;
	// Singletons, represented by a pointer to the set_univ
	int_t vars = 0;
	// Internal memory structures for lifting equalities from single variables
	static std::vector<std::pair<int_t, int_t>> eq_lift_hi;
	static std::vector<std::pair<int_t, int_t>> eq_lift_lo;

	static void lift_imps(poset &p, poset &hi, poset &lo);
	static void lift_vars(poset &p, int_t v, poset &hi, poset &lo);
	static void lift_eqs(poset &p, int_t v, poset &hi, poset &lo);
  public:
	// Indicates if the poset has an associated BDD part
	bool pure = false;
	// Indicates the smallest variable in the poset
	int_t v = 0;

	poset () = default;

	//Creates single variable poset
	explicit poset (int_t v) : vars(v), pure(true), v(v) {}

	friend std::hash<poset>;
	bool operator==(const poset &p) const;

	static void init(int n) {
		P.emplace_back(); P.emplace_back();
		NP.emplace_back(); NP.emplace_back();
		pu::init(n);
		pp::init();
		ps::init();
	};

	static bool resize (int n) {
		return pu::resize(n);
	};

	static int_t size () {
		// The only data structure that needs size control is union find
		return pu::size();
	};

	static poset lift(int_t v, poset &&hi, poset &&lo);
	//static poset eval (int_t v, poset& p);
	static bool insert_var(poset &p, int_t v);
	static poset insert_var(poset &&p, int_t v);
	static void insert_imp(poset &p, std::pair<int_t, int_t> &el);
	static void insert_imp(poset &p, int_t fst, int_t snd);
	static void insert_eq(poset &p, int_t v1, int_t v2);
	static poset get(int_t pos, bool negated);

	inline static bool is_empty(poset &p) {
		return p.eqs + p.imps + p.vars == 0;
	}

	inline static bool only_vars(poset &p) {
		return p.eqs + p.imps == 0 && p.vars > 0;
	}
};

#endif  // TML_POSET_H
