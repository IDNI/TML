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

#include <vector>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include <functional>
#include <cctype>
#include <ctime>
#include <memory>
#include <locale>
#include <codecvt>
#include <fstream>
#include <iterator>
#include <optional>
#include <ranges>
#include <functional>
#include <optional>
#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt_squaring.h"

using namespace std;


/* Constructs a map with head/body information. In our case, the body is the 
 * first element of the vector of terms and the body the remaining terms. */

rule_index index_rules(const flat_prog &fp) {
	rule_index c;
	for (auto const &t: fp) {
		if (is_goal(t) || is_fact(t)) continue;
		if (c.contains(get_rel_info(t))) c[get_rel_info(t)].insert(t);
		else c[get_rel_info(t)] = set<flat_rule> {t};
	}
	return c;
}

/* Check if it the given substitution is compatible. */

inline bool is_compatible(int_t s, int_t u) {
	return (u >= 0 && (s <= 0 || u == s)) || (u < 0 && s < 0);
}

/* Apply a given unification to a given tail of a relation. */

bool apply_unification(unification &u, flat_rule &fr) {
	for (auto &t: fr) 
		for(size_t i = 1; i < t.size(); ++i) 
			if (u.contains(t[i])) 
				t[i] = u.at(t[i]);
	return true;
}

/* Compute the unification of two terms. To do this we take into account that
 * we are only considering the case where both term have the same symbol,  
 * the same arity and there are no recursive structures (they are flat). 
 * The procedure is as follows:
 * - a=a or X=X continue,
 * - a=X or X=a add X->a (apply X->a to the rest of the arguments)
 * - X=Y add X->Y
 * See [Martelli, A.; Montanari, U. (Apr 1982). "An Efficient Unification 
 * Algorithm". ACM Trans. Program. Lang. Syst. 4 (2): 258–282] for details. */

optional<unification> unify(const term &t1, const term &t2) {
	unification u;
	for (size_t i= 0; i < t1.size(); ++i) {
		if (t1[i] > 0 /* is cte */ && t2[i] > 0 /* is cte */) {
			if (t1[i] != t2[i]) return optional<unification>();
		} else if (t1[i] < 0 /* is var */ && t2[i] > 0 /* is constant */) { 
			if (u.contains(t1[i])) {
				if (u[t1[i]] == t2[i]) continue;
				else return optional<unification>();
			}
			u[t1[i]] = t2[i]; continue; 
		} else if (t1[i] > 0 /* is constant */ && t2[i] < 0 /* is var */) { 
			if (u.contains(t1[i])) {
				if (u[t1[i]] == t2[i]) continue;
				else return optional<unification>();
			}
			u[t2[i]] = t1[i]; continue; 
		} else {
			if (u.contains(t1[i])) {
				if (u[t1[i]] == t2[i]) continue;
				else return optional<unification>();
			}
			u[t1[i] /* is var */ ]  = t2[i] /* is var */;
		}
	}
	return optional<unification>(u);
}

/* Copmpute the last var used in the given rule. */

int_t get_last_var(const flat_rule &r) {
	int_t lst = 0;
	for (auto &t: r) for (auto i: t) lst = (i < lst) ? i : lst;
	return lst;
}

/* Renames all variables of a rule. */

flat_rule rename_rule_vars(const flat_rule &fr, int_t& lv) {
	flat_rule nfr(fr);
	map<int_t, int_t> sbs;
	for (auto &t: nfr) for (size_t i = 0; i != t.size(); ++i)
		if (!sbs.contains(t[i]) && t[i] < 0) sbs[t[i]] = --lv, t[i] = sbs[t[i]];
	return nfr;
}

/* Returns the squaring of a rule given a selection for the possible substitutions. */

void square_rule(flat_rule &fr, selection &sels, flat_prog &fp) {
	// TODO check fr is a datalog program
	flat_rule sfr; 
	// Add the head of the existing rule
	sfr.emplace_back(fr[0]);
	auto lv = get_last_var(fr);
	bool unified = true;
	for (size_t i = 0; i < sels.size(); ++i) {
		auto rfr = rename_rule_vars(sels[i], lv);
		if (auto u = unify(fr[i + 1], rfr[0])) {
			#ifndef DELETE_ME
			cout << "UNIFICATIOIN: {";
			for (auto &[f, s]: *u) {
				cout << "{" << f << ':' << s << "}, ";
				cout << "}\n";
			}
			#endif // DELETE_ME
			unified = unified && apply_unification(*u, sfr);
			unified = unified && apply_unification(*u, rfr);
			if (!unified) break;
			sfr.insert(sfr.end(), ++rfr.begin(), rfr.end()); 
		} else { unified = false; break; }
	}
	if (!unified) fp.insert(fr);
	else fp.insert(sfr);
}

/* Returns the squaring of a rule  */

void square_rule(flat_rule &fr, selection &sels, const rule_index &idx, 
		flat_prog &fp, size_t pos = 0) {
	if (!idx.contains(get_rel_info(fr))) {
		fp.insert(fr);
		return;
	}
	// If we have selected all possible alternatives proceed with
	// the squaring of the rule
	if (pos == sels.size()) {
		square_rule(fr, sels, fp);
		return;
	}
	// otherwise, try all the possible selections
	for (auto &o: idx.at(get_rel_info(fr[pos + 1]))) {
		sels[pos] = o; 
		square_rule(fr, sels, idx, fp, pos + 1);
	}
}

/* Returns the squaring of a rule. As square_program automatically 
 * deals with facts and goals, we could assume that the body is not empty. */

void square_rule(flat_rule &fr, flat_prog &fp, const rule_index &idx) {
	// Cache vector with the selected rules to be used in squaring
	selection sels(fr.size());
	square_rule(fr, sels, idx, fp);
}

flat_prog square_program(const flat_prog &fp) {
	// New flat_prog holding the squaring of fp
	flat_prog sqr;
	// Cache info for speed up the squaring holding a map between heads
	// and associated bodies
	auto idx = index_rules(fp);
	for (auto fr: fp) {
		if(is_fact(fr) || is_goal(fr)) 
			sqr.insert(fr);
		else square_rule(fr, sqr, idx);
	}
	return sqr;
}
