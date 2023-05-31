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

/*
 * This class implements a persistent array. A pointer to an instance of an array
 * which points to a position in the universe, called storage in this class.
 * An instance of an array is a difference chain. A normal array is laying underneath
 * and the difference chain says which values the array holds at which position.
 * If a particular array is accessed this difference chain is traversed and the
 * actual array then holds all values according to this chain. Any consecutive access
 * to the array neglects the difference chain, since the array is already correct,
 * since it was accessed before.
 */
class PersistentArray {
	typedef std::vector<int_t> storage;

	int_t p = -1, v = -1, diff = -1;

	static void update(storage &arr, int t);
  public:
	PersistentArray() : diff(-1) {}

	PersistentArray(int_t pos, int_t val, int_t a) : p(pos), v(val),
							 diff(a) {}

	friend class persistent_union_find;

	// Place initial values into array of size n
	static int_t
	init(storage &arr, int_t n, int_t(*f)(int_t));

	static void
	resize(storage &arr, int_t n, std::function<int_t(int_t)> &&f) {
		arr.reserve(n);
		for (int_t i = arr.size(); i < n; ++i) arr.emplace_back(f(i));
	}

	// Get the value at position pos in the array represented by t.
	// c is the pointer to the current array represented
	static int_t get(storage &arr, int_t& c, int_t t, int_t pos, bool reset_to_num);
	// Set the value at position pos to val in the array represented by t
	// c is the pointer to the current array represented
	static int_t set(storage &arr, int_t& c, int_t t, int_t pos, int_t val, bool reset_to_num);
	// Given the current array c and the goal array t, make t the current array
	static void reroot(storage &arr, int_t& c, int_t t, bool reset_to_num);

	static int_t size(storage &arr) { return (int_t) arr.size(); }
};

class pu_iterator;

/*
 * This class implements a persistent union find data structure that additionally
 * supports negation, set retrieval and removal of sets. The underlying array
 * is the persistent array data structure introduced above.
 */
class persistent_union_find {
	using pu = persistent_union_find;
	using pa = PersistentArray;

	// Persistent arrays which this union find needs
	// parent_s saves the parent relationship of elements
	// links_s saves the linking between elements to retrieve sets
	// and hashes_s saves the hashes of each set that is present in the
	// union find data structure
	static std::vector<int_t> parent_s, link_s, hashes_s;
	// Pointers to the current instance of the persistent array
	static int current_parent, current_link, current_hash;
	// Pointers to the correct version of the persistent arrays for this particular
	// union find instance
	mutable int_t arr_pt;
	int_t link_pt;
	int_t hash_pt;
	// The hash of this union find instance. The hash is obtained by adding
	// the squares of numbers contained in each set and by then xor-ing all
	// obtained set hashes. This hash is commutative and incremental which
	// is a must requirement for the hash function.
	int_t hash = 0;

	// Initialisation of the persistent union find data structure
	explicit persistent_union_find(int_t n) {
		arr_pt = pa::init(parent_s, n, [](int_t i) { return i; });
		link_pt = pa::init(link_s, n, [](int_t i) { return i; }) + 1;
		hash_pt = pa::init(hashes_s, n, [](int_t i) { return 0; }) + 2;
		current_parent = 0; current_link = 1; current_hash = 2;
	}

	// Create pu taking the change from setting value at position x to y into account
	explicit persistent_union_find(int_t a_ptr, int_t l_ptr, int_t h_ptr,
	int_t h_old, int_t x, int_t y,
		int_t hash_x, int_t hash_y) {
		arr_pt = a_ptr, link_pt = l_ptr, hash_pt = h_ptr;
		hash = h_old ^ hash_x ^ hash_y ^ hash_set(x, y, hash_x, hash_y);
	}

	// Canonically add a union find instance to the universe
	static int_t add(pu &uf);
	// Update the union find t by setting the value at x to y
	// while assuming that x and y are root nodes of sets
	// y is the new parent of x
	static int_t update(const pu &t, int_t x, int_t y);
	// Update the linking when the value of x is set to y in t
	static int_t update_link(const pu &t, int_t x, int_t y);
	// Find the root of elem in t
	static int_t find(const pu &t, int_t elem);
	// Return an iterator to the elements equal to x in the union find uf
	static pu_iterator get_equal(pu &uf, int_t x);
	// Helper function for merge sort
	static pu_iterator
	HalfList(const pu_iterator &start, const pu_iterator &end);
	static int_t
	SortedMerge(pu_iterator &a, pu_iterator &b, int_t a_end, int_t b_end,
		    int_t pos, bool negated);
  public:
	// Sort the linking list of a set
	static int_t
	MergeSort(pu_iterator start, const pu_iterator &end);
	persistent_union_find() = delete;
	bool operator==(const pu &) const;
	friend std::hash<pu>;
	friend pu_iterator;
	// Initialize the persistent union find data structure
	static void init(int_t n);
	// Return the root of elem in t
	static int_t find(int_t t, int_t elem);
	// Return pointer to union find in which the sets x and y are merged
	static int_t merge(int_t t, int_t x, int_t y);
	// Return a pointer to union find in which the elements from s are merged
	static int_t merge_set (int_t t, std::vector<int_t>& s);
	// Return a pointer to union find holding the intersection between t1 and t2
	static int_t intersect(int_t t1, int_t t2);
	// Check if the two union find structures are equal
	static bool equal(int_t t, int_t x, int_t y);
	// Return an iterator over the elements which are equal to x in t including x
	static pu_iterator get_equal(int_t t, int_t x);
	// Return a pointer to a union find in which the set containing x is removed
	static int_t rm_equal(int_t t, int_t x);
	// Check if the set containing x in t is a singleton set
	static bool is_singleton(int_t t, int_t x);
	// Return a vector of all elements that can be found in t
	static std::vector<int_t> elems(int_t t);
	// Set a new size for the underlying arrays of the union find data structure
	static bool resize(int_t n);
	// Return the size of the underlying arrays
	static int_t size();

	//Hash root representatives of two sets
	inline static int_t
	hash_set(int_t x, int_t y, int_t x_hash, int_t y_hash) {
		// A singleton set still has hash 0
		// Singleton sets are hashed to their square
		return ((x_hash == 0 ? x * x : x_hash) +
			(y_hash == 0 ? y * y : y_hash));
	}

	// Print the union find data uf structure to os
	static void print(int_t uf, std::ostream &os);
	static void print(pu &uf, std::ostream &os);
};

/*
 * This class implements an iterator over a set in the persistent union find data
 * structure.
 */
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
