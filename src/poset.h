#ifndef TML_POSET_H
#define TML_POSET_H

#include <unordered_map>
#include <vector>
#include <memory>
#include <functional>
#include "defs.h"

class pu_iterator;

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
	typedef std::vector<int_t> storage;

	int_t p = -1, v = -1, diff = -1;

	static void update(storage &arr, int t);
  public:
	PersistentArray() : diff(-1) {}

	PersistentArray(int_t pos, int_t val, int_t a) : p(pos), v(val),
							 diff(a) {}

	friend class PersistentUnionFind;

	static inline int_t
	init(storage &arr, int_t n, std::function<int_t(int_t)> &&f);

	static void
	resize(storage &arr, int_t n, std::function<int_t(int_t)> &&f) {
		arr.reserve(n);
		for (int_t i = arr.size(); i < n; ++i) arr.emplace_back(f(i));
	}

	static int_t get(storage &arr, int_t& c, int_t t, int_t pos, bool reset_to_num);
	static int_t set(storage &arr, int_t& c, int_t t, int_t pos, int_t val, bool reset_to_num);
	static void reroot(storage &arr, int_t& c, int_t t, bool reset_to_num);

	static int_t size(storage &arr) { return (int_t) arr.size(); }
};

class PersistentUnionFind {
	typedef PersistentUnionFind pu;
	typedef PersistentArray pa;

	static std::vector<int_t> parent_s, link_s, hashes_s;
	static int current_parent, current_link, current_hash;
	mutable int_t arr_pt;
	int_t link_pt;
	int_t hash_pt;
	int_t hash = 0;

	explicit PersistentUnionFind(int_t n) {
		arr_pt = pa::init(parent_s, n, [](int_t i) { return i; });
		link_pt = pa::init(link_s, n, [](int_t i) { return i; }) + 1;
		hash_pt = pa::init(hashes_s, n, [](int_t i) { return 0; }) + 2;
		current_parent = 0; current_link = 1; current_hash = 2;
	}

	// Create puf taking the change from setting value at position x to y into account
	explicit PersistentUnionFind(int_t a_ptr, int_t l_ptr, int_t h_ptr,
				     int_t h_old, int_t x, int_t y,
				     int_t hash_x, int_t hash_y) {
		arr_pt = a_ptr, link_pt = l_ptr, hash_pt = h_ptr;
		hash = h_old ^ hash_x ^ hash_y ^ hash_set(x, y, hash_x, hash_y);
	}

	static int_t add(pu &uf);
	static int_t update(const pu &t, int_t x, int_t y);
	/*static void split_set(std::vector<int_t> &s, pu &uf, int_t root);
	static void
	split_hashes(int_t root_x, int_t root_y, int_t hash_x,
		     int_t hash_y, int_t count_x, int_t count_y,
		     int_t prev_root, pu &uf);
	static void split_linking(std::vector<int_t> &s, pu &uf,
				  int_t root);*/
	static int_t update_link(const pu &t, int_t x, int_t y);
	static int_t find(const pu &t, int_t elem);
	static pu_iterator get_equal(pu &uf, int_t x);
	static pu_iterator
	HalfList(const pu_iterator &start, const pu_iterator &end);
	static int_t
	SortedMerge(pu_iterator &a, pu_iterator &b, int_t a_end, int_t b_end,
		    int_t pos, bool negated);
  public:
	static int_t
	MergeSort(pu_iterator start, const pu_iterator &end);
	PersistentUnionFind() = delete;
	bool operator==(const pu &) const;
	friend std::hash<pu>;
	friend pu_iterator;

	static void init(int_t n);
	static int_t find(int_t t, int_t elem);
	static int_t merge(int_t t, int_t x, int_t y);
	static int_t merge_set (int_t t, std::vector<int_t>& s);
	static int_t intersect(int_t t1, int_t t2);
	static bool equal(int_t t, int_t x, int_t y);
	static pu_iterator get_equal(int_t t, int_t x);
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

	static void print(int_t uf, std::ostream &os);
	static void print(pu &uf, std::ostream &os);
};

class pu_iterator {
	using pa = PersistentArray;
	using pu = PersistentUnionFind;
	int_t val;
	int_t end_val;
	bool negate:1;
	bool looped:1;
	pu& uf;

  public:
	pu_iterator(pu &puf, int_t val_) : val(val_), end_val(val_),
					   negate(val_ < 0), looped(false),
					   uf(puf) {};

	pu_iterator(const pu_iterator &) = default;

	friend pu;

	pu_iterator &operator++() {
		if (!looped) looped = true;
		val = pa::get(pu::link_s, pu::current_link, uf.link_pt, abs(val), true);
		val = negate ? -val : val;
		if ((negate ? -val : val) < 0) negate = !negate;
		return *this;
	}

	int_t operator*() const { return val; }

	bool operator==(const pu_iterator &other) const {
		return abs(val) == abs(other.val) && looped == other.looped;
	}

	bool operator!=(const pu_iterator &other) const {
		return abs(val) != abs(other.val) || looped != other.looped;
	}

	void update_pos (int_t v) {
		if(v < 0 && val > 0 || v > 0 && val < 0)
			negate = !negate;
		val = v;
	}

	pu_iterator begin() { return {uf, end_val}; }

	pu_iterator end() {
		auto it = pu_iterator(uf, end_val);
		it.looped = true;
		return it;
	}
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
	static void print(int_t set_id, std::ostream &os);
};

// The representative of a set of pairs is its smallest element
struct PersistentPairs {
	// Element in set
	// If e is (0,0) we are dealing with the empty set
	std::pair<int_t, int_t> e;
	// Pointer to next element
	// If n is 0 we have reached the end of a set
	int_t n;
	PersistentPairs() = delete;

	PersistentPairs(std::pair<int_t, int_t> &&e_, int_t n_) : e(move(e_)),
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
	static int_t
	implies(int_t set_id, int_t elem, bool del, std::vector<int_t> &imp);
	static int_t
	all_implies(int_t set_id, int_t elem, bool del,
		    std::vector<int_t> &all_imp);
	static int_t next(int_t set_id);
	static PersistentPairs get(int_t set_id);
	static void print(int_t set_id, std::ostream &os);
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
	static std::unordered_map<int_t,int_t> eq_lift_hi;
	static std::unordered_map<int_t,int_t> eq_lift_lo;
	static std::vector<std::pair<int_t, int_t>> eq_lift;

	static void lift_imps(poset &p, poset &hi, poset &lo);
	static void lift_vars(poset &p, int_t v, poset &hi, poset &lo);
	static void lift_eqs(poset &p, int_t v, poset &hi, poset &lo);
  public:
	// Indicates if the poset has an associated BDD part
	bool pure = false;
	// Indicates the smallest variable in the poset
	int_t v = 0;

	poset() = default;

	//Creates single variable poset
	explicit poset(int_t v) : pure(true), v(abs(v)) { insert_var(*this, v); }

	explicit poset(bool isPure) : pure(isPure) {}

	friend std::hash<poset>;
	bool operator==(const poset &p) const;

	static void init(int n) {
		P.emplace_back(true);
		P.emplace_back(true);
		NP.emplace_back(true);
		NP.emplace_back(false);
		pu::init(n);
		pp::init();
		ps::init();
	};

	static bool resize(int n) {
		return pu::resize(n);
	};

	static int_t size() {
		// The only data structure that needs size control is union find
		return pu::size();
	};

	static poset lift(int_t v, int_t h, int_t l);
	static poset eval(poset &p, int_t v);
	static bool insert_var(poset &p, int_t v);
	static poset insert_var(poset &&p, int_t v);
	static void insert_imp(poset &p, std::pair<int_t, int_t> &el);
	static void insert_imp(poset &p, int_t fst, int_t snd);
	static void insert_eq(poset &p, int_t v1, int_t v2);
	static poset get(int_t pos);
	static void print(poset &p, std::ostream &os);

	inline static bool is_empty(poset &p) {
		return p.eqs + p.imps + p.vars == 0;
	}

	inline static bool only_vars(poset &&p) {
		return p.eqs + p.imps == 0 && p.vars > 0;
	}
};

#endif  // TML_POSET_H