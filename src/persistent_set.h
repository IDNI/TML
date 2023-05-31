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
	// Create a persistent set node and add it canonically to the universe
	static int_t add(int_t e, int_t n);
	// Place the empty set in the universe
	static void init();
	// Insert elem into the persistent set represented by set_id
	static int_t insert(int_t set_id, int_t elem);
	// Remove elem from the persistent set represented by set_id
	static int_t remove(int_t set_id, int_t elem);
	// Check if the set represented by set_id is empty
	static bool empty(int_t set_id);
	// Check if the set represented by set_id contains elem
	static bool contains(int_t set_id, int_t elem);
	// Return the pointer to the universe where elem was found in set_id
	static int_t find(int_t set_id, int_t elem);
	// Get the pointer of the next element that is contained in set_id
	static int_t next(int_t set_id);
	// Get the persistent set node from the set_id
	static persistent_set get(int_t set_id);
	// Print the persistent set represented by set_id into os
	static void print(int_t set_id, std::ostream &os);
	// Return the size of the set represented by set_id
	static int_t size(int_t set_id);
};

#endif //TML_PERSISTENT_SET_H
