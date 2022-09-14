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

#ifndef __TRANSFORM_OPT_COMMON_H__
#define __TRANSFORM_OPT_COMMON_H__

#include <map>
#include <tuple>
#include <vector>
#include <set>
#include "ir_builder.h"

using flat_rule = std::vector<term>;
using rel_arity = std::tuple<int_t, size_t>;
using rule_index = std::map<rel_arity, std::set<flat_rule>>;
using unification = std::map<int_t, int_t>;
using selection = std::vector<flat_rule>;

/* Get relation info from the head term in a way suitable for be used as key. */

inline rel_arity get_rel_info(const term &t);

/* Get relation info from a flat rule in a way suitable to be used as a key. */

inline rel_arity get_rel_info(const flat_rule &t);

/* Returns true if the vector of terms correspond to a fact, false otherwise. */

inline bool is_fact(const flat_rule &r);

/* Returns true if the vector of terms correspond to a goal, false otherwise. */

inline bool is_goal(const flat_rule &r);

#endif // __TRANSFORM_OPT_COMMON_H__