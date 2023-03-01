#ifndef TML_PERSISTENT_UNION_FIND_H
#define TML_PERSISTENT_UNION_FIND_H

#include "defs.h"
#include <functional>

template<>
struct std::hash<class persistent_union_find> {
	size_t operator()(const persistent_union_find &) const;
};

template<>
struct std::hash<std::pair<int_t, int_t>> {
	size_t operator()(const std::pair<int_t, int_t> &) const;
};

class PersistentArray {
	typedef std::vector<int_t> storage;

	int_t p = -1, v = -1, diff = -1;

	static void update(storage &arr, int t);
  public:
	PersistentArray() : diff(-1) {}

	PersistentArray(int_t pos, int_t val, int_t a) : p(pos), v(val),
							 diff(a) {}

	friend class persistent_union_find;

	static int_t
	init(storage &arr, int_t n, int_t(*f)(int_t));

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

class pu_iterator;

class persistent_union_find {
	using pu = persistent_union_find;
	using pa = PersistentArray;

	static std::vector<int_t> parent_s, link_s, hashes_s;
	static int current_parent, current_link, current_hash;
	mutable int_t arr_pt;
	int_t link_pt;
	int_t hash_pt;
	int_t hash = 0;

	explicit persistent_union_find(int_t n) {
		arr_pt = pa::init(parent_s, n, [](int_t i) { return i; });
		link_pt = pa::init(link_s, n, [](int_t i) { return i; }) + 1;
		hash_pt = pa::init(hashes_s, n, [](int_t i) { return 0; }) + 2;
		current_parent = 0; current_link = 1; current_hash = 2;
	}

	// Create puf taking the change from setting value at position x to y into account
	explicit persistent_union_find(int_t a_ptr, int_t l_ptr, int_t h_ptr,
	int_t h_old, int_t x, int_t y,
		int_t hash_x, int_t hash_y) {
		arr_pt = a_ptr, link_pt = l_ptr, hash_pt = h_ptr;
		hash = h_old ^ hash_x ^ hash_y ^ hash_set(x, y, hash_x, hash_y);
	}

	static int_t add(pu &uf);
	static int_t update(const pu &t, int_t x, int_t y);
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
	persistent_union_find() = delete;
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
	static bool is_singleton(int_t t, int_t x);
	static std::vector<int_t> elems(int_t t);
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
	using pu = persistent_union_find;
	int_t val;
	int_t end_val;
	bool negate:1;
	bool looped:1;
	int_t t;

  public:
	pu_iterator(int_t puf, int_t val_) : val(val_), end_val(val_),
					     negate(val_ < 0), looped(false),
					     t(puf) {};

	pu_iterator(const pu_iterator &) = default;

	friend pu;

	pu_iterator &operator++();

	int_t operator*() const { return val; }

	bool operator==(const pu_iterator &other) const {
		return abs(val) == abs(other.val) && looped == other.looped;
	}

	bool operator!=(const pu_iterator &other) const {
		return abs(val) != abs(other.val) || looped != other.looped;
	}

	void update_pos (int_t v) {
		if((v < 0 && val > 0) || (v > 0 && val < 0))
			negate = !negate;
		val = v;
	}

	pu_iterator begin() { return {t, end_val}; }

	pu_iterator end() {
		auto it = pu_iterator(t, end_val);
		it.looped = true;
		return it;
	}
};

#endif //TML_PERSISTENT_UNION_FIND_H
