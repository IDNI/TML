#ifndef TML_PERSISTENT_SET_H
#define TML_PERSISTENT_SET_H

#include "defs.h"

struct persistent_set;

template<>
struct std::hash<persistent_set> {
	size_t operator()(const persistent_set &) const;
};

// The representative of a set of ints is its smallest element
struct persistent_set {
	// Element in set
	// If e is 0 we are dealing with the empty set
	int_t e;
	// Pointer to next element
	// If n is 0 we have reached the end of a set
	int_t n;
	persistent_set() = delete;

	persistent_set(int_t e_, int_t n_) : e(e_), n(n_) {}

	bool operator==(const persistent_set &) const;
	static int_t add(int_t e, int_t n);
	static void init();
	// The insertion will return 0, if the insertion causes a contradiction
	static int_t insert(int_t set_id, int_t elem);
	static int_t remove(int_t set_id, int_t elem);
	static bool empty(int_t set_id);
	static bool contains(int_t set_id, int_t elem);
	static int_t find(int_t set_id, int_t elem);
	static int_t next(int_t set_id);
	static persistent_set get(int_t set_id);
	static void print(int_t set_id, std::ostream &os);
};

#endif //TML_PERSISTENT_SET_H
