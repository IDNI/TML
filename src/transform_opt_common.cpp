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

#include "transform_opt_common.h"

using namespace std;

inline rel_arity get_rel_info(const term &t) {
	return make_tuple(t.tab, t.size());
}

inline rel_arity get_rel_info(const flat_rule &t) {
	return get_rel_info(t[0]);
}

inline bool is_fact(const flat_rule &r) {
	// Only one term and is not a goal
	return r.size() == 1 && !r[0].goal;
}

inline bool is_goal(const flat_rule &r) {
	// TODO consider remove defensive programming
	// Non empty and its a goal
	return !r.empty() && r[0].goal;
}
