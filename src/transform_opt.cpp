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
#include <map>
#include <set>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include <functional>
#include <cctype>
#include <ctime>
#include <locale>
#include <codecvt>
#include <fstream>

#include <optional>
#include <functional>

#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt.h"

using namespace std;


// starting node of the mutated progs log
mutated_prog::mutated_prog(raw_prog *p) : current(p) {}

// link to previous mutated prog
mutated_prog::mutated_prog(mutated_prog *m) : previous(m) {}

mutated_prog::mutated_prog(const mutated_prog &that) {
	this->current = that.current;
	this->previous = that.previous;
	this->deletions = that.deletions;
}

void mutated_prog::operator()(mutation& m) {
	// apply the mutation to the current mutated_prog
	m(*this);
}

mutated_prog*  mutated_prog::operator--() {
	return previous;
}

/*!
 * Collapse all valid raw rules into a vector.
 */ 
vector<raw_rule>  mutated_prog::get_rules() {
	vector<raw_rule> all;
	// get previous rules
	if (previous) {
		auto v = previous->get_rules();
		all.insert(all.end(), v.begin(), v.end());
	}
	// remove current deletions
	for (auto &r: deletions) {
		auto i = find(deletions.begin(), deletions.end(), &r);
		if (i != deletions.end()) deletions.erase(i);
	}
	// add current rules
	all.insert(all.end(), current->r.begin(), current->r.end());
	return all;
}

raw_prog  mutated_prog::to_raw_program() {
	if (!previous) {
		// remove current deletions
		for (auto &r: deletions) {
			auto i = find(current->r.begin(), current->r.end(), &r);
			if (i != current->r.end()) current->r.erase(i);
		}
		return *current;
	}
	auto p = (*previous).to_raw_program();
	for (auto &r: deletions) {
		auto i = find(current->r.begin(), current->r.end(), &r);
		if (i != current->r.end()) current->r.erase(i);
	}
	current->r.insert(current->r.end(), p.r.begin(), p.r.end());
	return *current;
}

best_solution::best_solution(cost_function &f): cost(f) {}

bool best_solution::bound(mutated_prog &p) {
	best_solution::bests[best_solution::cost(p)] = p;
	return false;
}

raw_prog best_solution::solution() {
	return (*bests.begin()).second.to_raw_program();
}

/*!
 * Optimize a mutated program
 */
void optimize(mutated_prog& mutated, bounder& bounder, set<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<mutation> mutations;
	for(brancher brancher: branchers) {
		auto proposed = brancher(mutated);
		mutations.insert(mutations.end(), proposed.begin(), proposed.end());
	}
	// for each subset of optimizations, compute the new mutated program,
	// bound the current mutation and try to optimize again if needed
	powerset_range subsets(mutations);
	for (auto it = subsets.begin(); it != subsets.end(); ++it) {
		mutated_prog new_mutated(mutated);
		for (auto mt = (*it).begin(); mt != (*it).end(); ++mt) (*mt)(new_mutated);
		if (bounder.bound(new_mutated)) {
			optimize(new_mutated, bounder, branchers);
		}
	}
}

/*!
 * Optimize a raw program
 */
raw_prog optimize(raw_prog& program, bounder& bounder, set<brancher>& branchers) {
	// the first mutated program just contain the original program as additions.
	mutated_prog mutated {&program};
	optimize(mutated, bounder, branchers);
	return bounder.solution();
}

/*!
 * Minimizes the queries as much as posible.
 */
template<typename F>
vector<mutation> brancher_minimize_queries(mutated_prog &mutated, const F &f) {
	vector<mutation> mutations;
	vector<raw_rule> minimized;
	vector<raw_rule> deletions;

	for (raw_rule &rr: mutated.current->r) {
		// remove the current rule and add the minimize one
		deletions.push_back(rr);
		// Do the maximal amount of query minimization on the query we are
		// about to admit. This should reduce the time cost of future
		// subsumptions.
		auto nrr = rr;
		minimize(nrr, f);
		// If the current rule has not been subsumed, then it needs to be
		// represented in the reduced rules.
		minimized.push_back(nrr);
	}
	auto m = [minimized, deletions](mutated_prog &m) {
		m.current->r.insert(m.current->r.end(), minimized.begin(), minimized.end());
		m.deletions.insert(m.deletions.end(), deletions.begin(), deletions.end());
	};
	mutations.push_back(m);
	return mutations;
}

/*! Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. 
 */
template<typename F>
vector<mutation> brancher_subsume_queries(mutated_prog &mp /*rp*/, const F &f) {
	vector<mutation> mutations;
	vector<raw_rule> reduced;
	for (raw_rule &rr : mp.get_rules()) {
		bool subsumed = false;
		for (auto nrr = reduced.begin(); nrr != reduced.end();) {
			if (f(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				auto l = [rr, nrr](mutated_prog &m) {
					m.current->r.insert(m.current->r.end(), rr);
					m.deletions.insert(m.deletions.end(), &(*nrr));
					return true;
				};
				mutations.push_back(l);
				subsumed = true;
				break;
			} else if (f(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				reduced.erase(nrr);
				// remove the subsumed rule and add the current rule
				auto l = [nrr](mutated_prog &m) {
					remove(m.current->r.begin(), m.current->r.end(), nrr);
					return true;
				};
				mutations.push_back(l);
			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if (!subsumed) reduced.push_back(rr);
	}
	return mutations;
}

vector<mutation> driver::brancher_subsume_queries_cqc(mutated_prog &mp) {
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqc(rr1, rr2);});
}

vector<mutation> driver::brancher_subsume_queries_cqnc(mutated_prog &mp) {
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqnc(rr1, rr2);});
}

vector<mutation> driver::brancher_split_heads(mutated_prog &mp) {
	vector<mutation> mutations;
	auto l = [this](mutated_prog &p) {
		to_dnf(*(p.current));
		return true;
	};
	mutations.push_back(l);
	return mutations;
}

vector<mutation> driver::brancher_split_bodys(mutated_prog &mp) {
	vector<mutation> mutations;
	auto l = [this](mutated_prog &p) {
		split_heads(*(p.current));
		return true;
	};
	mutations.push_back(l);
	return mutations;
}

/* Returns the intersection of the two given sets. I.e. all the elems
 * that occur in both sets. */

set<elem> set_intersection(const set<elem> &s1, const set<elem> &s2) {
	set<elem> res;
	set_intersection(s1.begin(), s1.end(), s2.begin(), s2.end(),
		inserter(res, res.end()));
	return res;
}

/* Returns the difference between the two given sets. I.e. the second
 * set removed with multiplicity from the first. */

set<elem> set_difference(const multiset<elem> &s1,
		const set<elem> &s2) {
	set<elem> res;
	set_difference(s1.begin(), s1.end(), s2.begin(), s2.end(),
		inserter(res, res.end()));
	return res;
}

/* Convert every rule in the given program to DNF rules. */

void driver::to_dnf(raw_prog &rp) {
	// Convert all FOL formulas to DNF
	for(int_t i = rp.r.size() - 1; i >= 0; i--) {
		raw_rule rr = rp.r[i];
		if(rr.is_form()) {
			rr.set_b({{to_dnf(*rr.prft, rp, collect_free_vars(rr))}});
		}
		rp.r[i] = rr;
	}
}


/* Make a term with behavior equivalent to the supplied first order
 * logic formula with the given bound variables. This might involve
 * adding temporary relations to the given program. */

raw_term driver::to_dnf(const raw_form_tree &t,
		raw_prog &rp, const set<elem> &fv) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem::fresh_temp_sym(d);

	switch(t.type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::UNIQUE:
			// Process the expanded formula instead
			return to_dnf(expand_formula_node(t, d), rp, fv);
		case elem::AND: {
			// Collect all the conjuncts within the tree top
			vector<const raw_form_tree *> ands;
			t.flatten_associative(elem::AND, ands);
			// Collect the free variables in each conjunct. The intersection
			// of variables between one and the rest is what will need to be
			// exported
			multiset<elem> all_vars(fv.begin(), fv.end());
			map<const raw_form_tree *, set<elem>> fvs;
			for(const raw_form_tree *tree : ands) {
				fvs[tree] = collect_free_vars(*tree);
				all_vars.insert(fvs[tree].begin(), fvs[tree].end());
			}
			vector<raw_term> terms;
			// And make a DNF rule listing them
			for(const raw_form_tree *tree : ands) {
				set<elem> nv = set_intersection(fvs[tree],
					set_difference(all_vars, fvs[tree]));
				terms.push_back(to_dnf(*tree, rp, nv));
			}
			// Make the representative rule and add to the program
			raw_rule nr(raw_term(part_id, fv), terms);
			rp.r.push_back(nr);
			// Hide this new auxilliary relation
			rp.hidden_rels.insert({ nr.h[0].e[0].e, nr.h[0].arity });
			break;
		} case elem::ALT: {
			// Collect all the disjuncts within the tree top
			vector<const raw_form_tree *> alts;
			t.flatten_associative(elem::ALT, alts);
			for(const raw_form_tree *tree : alts) {
				// Make a separate rule for each disjunct
				raw_rule nr(raw_term(part_id, fv), to_dnf(*tree, rp, fv));
				rp.r.push_back(nr);
				// Hide this new auxilliary relation
				rp.hidden_rels.insert({ nr.h[0].e[0].e, nr.h[0].arity });
			}
			break;
		} case elem::NOT: {
			return to_dnf(*t.l, rp, fv).negate();
		} case elem::EXISTS: {
			// Make the proposition that is being quantified
			set<elem> nfv = fv;
			const raw_form_tree *current_formula;
			set<elem> qvars;
			// Get all the quantified variables used in a sequence of
			// existential quantifiers
			for(current_formula = &t;
					current_formula->type == elem::EXISTS;
					current_formula = &*current_formula->r) {
				qvars.insert(*(current_formula->l->el));
			}
			nfv.insert(qvars.begin(), qvars.end());
			// Convert the body occuring within the nested quantifiers into DNF
			raw_term nrt = to_dnf(*current_formula, rp, nfv);
			// Make the rule corresponding to this existential formula
			for(const elem &e : qvars) {
				nfv.erase(e);
			}
			raw_rule nr(raw_term(part_id, nfv), nrt);
			rp.r.push_back(nr);
			// Hide this new auxilliary relation
			rp.hidden_rels.insert({ nr.h[0].e[0].e, nr.h[0].arity });
			return raw_term(part_id, nfv);
		} case elem::NONE: {
			return *t.rt;
		} case elem::FORALL: {
			const raw_form_tree *current_formula;
			set<elem> qvars;
			// Get all the quantified variables used in a sequence of
			// existential quantifiers
			for(current_formula = &t;
					current_formula->type == elem::FORALL;
					current_formula = &*current_formula->r) {
				qvars.insert(*(current_formula->l->el));
			}
			// The universal quantifier is logically equivalent to the
			// following (forall ?x forall ?y = ~ exists ?x exists ?y ~)
			sprawformtree equiv_formula =
				make_shared<raw_form_tree>(elem::NOT,
					make_shared<raw_form_tree>(*current_formula));
			for(const elem &qvar : qvars) {
				equiv_formula = make_shared<raw_form_tree>(elem::EXISTS,
					make_shared<raw_form_tree>(qvar), equiv_formula);
			}
			return to_dnf(raw_form_tree(elem::NOT, equiv_formula), rp, fv);
		} default:
			assert(false); //should never reach here
	}
	return raw_term(part_id, fv);
}

/* Function to iterate through the partitions of the given set. Calls
 * the supplied function with a vector of sets representing each
 * partition. If the supplied function returns false, then the iteration
 * stops. */

template<typename T, typename F> 
bool partition_iter(set<T> &vars, vector<set<T>> &partition, const F &f) {
	if (vars.empty()) return f(partition);
	const T nvar = *vars.begin();
	vars.erase(nvar);
	for (size_t i = 0; i < partition.size(); i++) {
		partition[i].insert(nvar);
		if(!partition_iter(vars, partition, f)) return false;
		partition[i].erase(nvar);
	}
	set<T> npart = { nvar };
	partition.push_back(npart);
	if(!partition_iter(vars, partition, f)) return false;
	partition.pop_back();
	vars.insert(nvar);
	return true;
}

/* Function to iterate through the given set raised to the given
 * cartesian power. The supplied function is called with each tuple in
 * the product and if it returns false, the iteration stops. */

template<typename T, typename F>
bool product_iter(const set<T> &vars, vector<T> &seq, size_t len, const F &f) {
	if (len == 0) return f(seq);
	for (const T &el : vars) {
		seq.push_back(el);
		if(!product_iter(vars, seq, len - 1, f)) return false;
		seq.pop_back();
	}
	return true;
}

/* Function to iterate through the power set of the given set. The
 * supplied function is called with each element of the power set and
 * if it returns false, the iteration stops. */

template<typename T, typename F> bool power_iter(set<T> &elts,
		set<T> &subset, const F &f) {
	if (elts.size() == 0) return f(subset);
	const T nelt = *elts.begin();
	elts.erase(nelt);
	// Case where current element will not be in subset
	if (!power_iter(elts, subset, f)) return false;
	if (subset.insert(nelt).second) {
		// Case where current element will be in subset
		if(!power_iter(elts, subset, f)) return false;
		subset.erase(nelt);
	}
	elts.insert(nelt);
	return true;
}

/* Takes a reference rule, its formula tree, and copies of both and
 * tries to eliminate redundant subtrees of the former using the latter
 * as scratch. Generally speaking, boolean algebra guarantees that
 * eliminating a subtree will produce a formula contained/containing
 * the original depending on the boolean operator that binds it and the
 * parity of the number of negation operators containing it. So we need
 * only apply the supplied query containment procedure for the reverse
 * direction to establish the equivalence of the entire trees. */

template<typename F>
raw_form_tree& minimize_aux(const raw_rule &ref_rule,
		const raw_rule &var_rule, raw_form_tree &ref_tree,
		raw_form_tree &var_tree, const F &f, bool ctx_sign) {
	typedef initializer_list<pair<raw_form_tree, raw_form_tree>> bijection;
	// Minimize different formulas in different ways
	switch(var_tree.type) {
		case elem::IMPLIES: {
			// Minimize the subtrees separately first. Since a -> b is
			// equivalent to ~a OR b, alter the parity of the first operand
			minimize_aux(ref_rule, var_rule, *ref_tree.l, *var_tree.l, f, !ctx_sign);
			minimize_aux(ref_rule, var_rule, *ref_tree.r, *var_tree.r, f, ctx_sign);
			const raw_rule &ref_rule_b = ref_rule.try_as_b();
			raw_form_tree orig_var = var_tree;
			// Now try eliminating each subtree in turn
			for (auto &[ref_tmp, var_tmp] : bijection
					{{raw_form_tree(elem::NOT, ref_tree.l),
						raw_form_tree(elem::NOT, orig_var.l)},
						{*ref_tree.r, *orig_var.r}})
				// Apply the same treatment as for a disjunction since this is
				// what an implication is equivalent to
				if(var_tree = var_tmp; ctx_sign ? f(ref_rule_b, var_rule.try_as_b()) : f(var_rule.try_as_b(), ref_rule))
					return ref_tree = ref_tmp;
			var_tree = orig_var;
			break;
		} case elem::ALT: {
			// Minimize the subtrees separately first
			minimize_aux(ref_rule, var_rule, *ref_tree.l, *var_tree.l, f, ctx_sign);
			minimize_aux(ref_rule, var_rule, *ref_tree.r, *var_tree.r, f, ctx_sign);
			const raw_rule &ref_rule_b = ref_rule.try_as_b();
			raw_form_tree orig_var = var_tree;
			// Now try eliminating each subtree in turn
			for (auto &[ref_tmp, var_tmp] : bijection
					{{*ref_tree.l, *orig_var.l}, {*ref_tree.r, *orig_var.r}})
				// If in positive context, eliminating disjunct certainly
				// produces smaller query, so check only the reverse. Otherwise
				// vice versa
				if(var_tree = var_tmp; ctx_sign ? f(ref_rule_b, var_rule.try_as_b()) : f(var_rule.try_as_b(), ref_rule_b))
					return ref_tree = ref_tmp;
			var_tree = orig_var;
			break;
		} case elem::AND: {
			// Minimize the subtrees separately first
			minimize_aux(ref_rule, var_rule, *ref_tree.l, *var_tree.l, f, ctx_sign);
			minimize_aux(ref_rule, var_rule, *ref_tree.r, *var_tree.r, f, ctx_sign);
			const raw_rule &ref_rule_b = ref_rule.try_as_b();
			raw_form_tree orig_var = var_tree;
			// Now try eliminating each subtree in turn
			for (auto &[ref_tmp, var_tmp] : bijection
					{{*ref_tree.l, *orig_var.l}, {*ref_tree.r, *orig_var.r}})
				// If in positive context, eliminating conjunct certainly
				// produces bigger query, so check only the reverse. Otherwise
				// vice versa
				if(var_tree = var_tmp; ctx_sign ? f(var_rule.try_as_b(), ref_rule_b) : f(ref_rule_b, var_rule.try_as_b()))
					return ref_tree = ref_tmp;
			var_tree = orig_var;
			break;
		} case elem::NOT: {
			// Minimize the single subtree taking care to update the negation
			// parity
			minimize_aux(ref_rule, var_rule, *ref_tree.l, *var_tree.l, f, !ctx_sign);
			break;
		} case elem::EXISTS: case elem::FORALL: {
			// Existential quantification preserves the containment relation
			// between two formulas, so just recurse. Universal quantification
			// is just existential with two negations, hence negation parity
			// is preserved.
			minimize_aux(ref_rule, var_rule, *ref_tree.r, *var_tree.r, f, ctx_sign);
			break;
		} default: {
			// Do not bother with co-implication nor uniqueness quantification
			// as the naive approach would require expanding them to a bigger
			// formula.
			break;
		}
	}
	return ref_tree;
}

/* Go through the subtrees of the given rule and see which of them can
 * be removed whilst preserving rule equivalence according to the given
 * containment testing function. */

template<typename F>
void minimize(raw_rule &rr, const F &f) {
	if (rr.is_fact() || rr.is_goal()) return;
	// Switch to the formula tree representation of the rule if this has
	// not yet been done for this is a precondition to minimize_aux. Note
	// the current form so that we can attempt to restore it afterwards.
	bool orig_form = rr.is_dnf();
	rr = rr.try_as_prft();
	// Copy the rule to provide scratch for minimize_aux
	raw_rule var_rule = rr;
	// Now minimize the formula tree of the given rule using the given
	// containment testing function
	// CHECK: the last true has been inserted to be able to compile... 
	minimize_aux(rr, var_rule, *rr.prft, *var_rule.prft, f, true);
	// If the input rule was in DNF, provide the output in DNF
	if (orig_form) rr = rr.try_as_b();
}


/* Collect the variables used in the given terms and return. */

void collect_vars(const raw_term &rt, set<elem> &vars) {
	for (const elem &e : rt.e) if(e.type == elem::VAR) vars.insert(e);
}

/* Collect the variables used in the given terms and return. */

template <class InputIterator>
void collect_vars(InputIterator first, InputIterator last, set<elem> &vars) {
	for (; first != last; first++) collect_vars(*first, vars);
}

/* Collect the variables used in the head and the positive terms of the
 * given rule and return. */

void collect_vars(const raw_rule &rr, set<elem> &vars) {
	collect_vars(rr.h[0], vars);
	for (const raw_term &tm : rr.b[0]) collect_vars(tm, vars);
}


/* Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. */

template<typename F>
void subsume_queries(raw_prog &rp, const F &f) {
	vector<raw_rule> reduced_rules;
	for (raw_rule &rr : rp.r) {
		bool subsumed = false;

		for (auto nrr = reduced_rules.begin(); nrr != reduced_rules.end();) {
			if (f(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				subsumed = true;
				break;
			} else if (f(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				nrr = reduced_rules.erase(nrr);
			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if (!subsumed) {
			// Do the maximal amount of query minimization on the query we are
			// about to admit. This should reduce the time cost of future
			// subsumptions.
			minimize(rr, f);
			// If the current rule has not been subsumed, then it needs to be
			// represented in the reduced rules.
			reduced_rules.push_back(rr);
		}
	}
	rp.r = reduced_rules;
}

void driver::subsume_queries_cqc(raw_prog &rp) {
	subsume_queries(rp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqc(rr1, rr2);});
}

void driver::subsume_queries_cqnc(raw_prog &rp) {
	subsume_queries(rp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqnc(rr1, rr2);});
}

#ifdef WITH_Z3

void driver::subsume_queries_z3(raw_prog &rp){
	subsume_queries(rp,
		[&](const raw_rule &rr1, const raw_rule &rr2)
			{return check_qc_z3(rr1, rr2, z3_ctx);});
}

#endif


/* Checks if the body of the given rule is conjunctive. */

bool is_cq(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if (rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if (rr.h[0].neg) return false;
	// Ensure that this rule is a proper rule
	if (!rr.is_dnf()) return false;
	// Ensure that each body term is positive and is a relation
	for (const raw_term &rt : rr.b[0]) {
		if (rt.neg || rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* Checks if the body of the given rule is conjunctive with negation. */

bool is_cqn(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if (rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if (rr.h[0].neg) return false;
	// Ensure that this rule is a proper rule
	if (!rr.is_dnf()) return false;
	// Ensure that each body term is a relation
	for (const raw_term &rt : rr.b[0]) {
		if (rt.extype != raw_term::REL) return false;
	}
	return true;
}

/*!
 * Checks if rr1 and rr2 are both conjunctive formulas and there exists
 * and homomorphism from rr2 to rr1.
 * 
 * If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. 
 */
bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t d;
	// Check that rules have correct format
	if (is_cq(rr1) && is_cq(rr2) &&
			get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0])) {
		o::dbg() << "CQC Testing if " << rr1 << " <= " << rr2 << endl;

		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);

		// Build up the queries necessary to check homomorphism.
		set<raw_term> edb(frozen_rr1.b[0].begin(), frozen_rr1.b[0].end());
		o::dbg() << "Canonical Database: " << edb << endl;
		raw_prog nrp(dict);
		nrp.r.push_back(rr2);

		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		set<raw_term> results;
		tables::run_prog_wedb(edb, nrp, d, opts, results);
		for (const raw_term &res : results) {
			if (res == frozen_rr1.h[0]) {
				// If the frozen head is found, then there is
				// a homomorphism between the two rules.
				o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
				return true;
			}
		}
		// If no frozen head found, then there is no homomorphism.
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
	}
	return false;
}

/*!
 * Checks if rr1 and rr2 are both conjunctive formulas and there exists
 * and homomorphism from rr2 to rr1.
 * 
 * If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. 
 */
bool driver::o2_cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t d;
	// Check that rules have correct format
	if (is_cq(rr1) && is_cq(rr2) &&
			get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0])) {
		o::dbg() << "CQC Testing if " << rr1 << " <= " << rr2 << endl;

		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);

		// Build up the queries necessary to check homomorphism.
		set<raw_term> edb(frozen_rr1.b[0].begin(), frozen_rr1.b[0].end());
		o::dbg() << "Canonical Database: " << edb << endl;
		raw_prog nrp(dict);
		nrp.r.push_back(rr2);

		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		set<raw_term> results;
		tables::run_prog_wedb(edb, nrp, d, opts, results);
		for (const raw_term &res : results) {
			if (res == frozen_rr1.h[0]) {
				// If the frozen head is found, then there is
				// a homomorphism between the two rules.
				o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
				return true;
			}
		}
		// If no frozen head found, then there is no homomorphism.
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
	}
	return false;
}

/*!
 * If rr1 and rr2 are both conjunctive queries with negation, check that
 * rr1 is contained by rr2. 
 * 
 * The implementation is based in the Levy-Sagiv test. 
 */
bool driver::cqnc(const raw_rule &rr1, const raw_rule &rr2) {
	// Check that rules have correct format
	if (!(is_cqn(rr1) && is_cqn(rr2) &&
		get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0]))) return false;

	o::dbg() << "CQNC Testing if " << rr1 << " <= " << rr2 << endl;

	set<elem> vars;
	collect_vars(rr1, vars);
	vector<set<elem>> partition;

	// Do the Levy-Sagiv test
	bool contained = partition_iter(vars, partition,
		[&](const vector<set<elem>> &partition) -> bool {
			// Print the current partition
			o::dbg() << "Testing partition: ";
			for (const set<elem> &s : partition) {
				o::dbg() << "{";
				for (const elem &e : s) {
					o::dbg() << e << ", ";
				}
				o::dbg() << "}, ";
			}
			o::dbg() << endl;

			// Create new dictionary so that symbols created for these tests
			// do not affect final program
			dict_t d;

			// Map each variable to a fresh symbol according to the partition
			map<elem, elem> subs;
			for (const set<elem> &part : partition) {
				elem pvar = elem::fresh_sym(d);
				for (const elem &e : part) {
					subs[e] = pvar;
				}
			}
			raw_rule subbed = freeze_rule(rr1, subs, d);
			set<raw_term> canonical, canonical_negative;
			// Separate the positive and negative subgoals. Note the symbols
			// supplied to the subgoals.
			for (raw_term &rt : subbed.b[0]) {
				if (rt.neg) {
					rt.neg = false;
					canonical_negative.insert(rt);
					rt.neg = true;
				} else canonical.insert(rt);
			}
			// Print the canonical database
			o::dbg() << "Current canonical Database: ";
			for (const raw_term &rt : canonical) {
				o::dbg() << rt << ", ";
			}
			o::dbg() << endl;
			// Does canonical database make all the subgoals of subbed true?
			for (raw_term &rt : subbed.b[0]) {
				if (rt.neg) {
					// If the term in the rule is negated, we need to make sure
					// that it is not in the canonical database.
					rt.neg = false;
					if (canonical.find(rt) != canonical.end()) {
						o::dbg() << "Current canonical database causes its source query to be inconsistent."
							<< endl;
						return true;
					}
					rt.neg = true;
				}
			}
			// Collect the symbols/literals from the freeze map
			set<elem> symbol_set;
			for (const auto &[elm, sym] : subs) {
				symbol_set.insert(sym);
				// Finer control over elements in the universe is required to
				// make this algorithm work with unsafe negations. In
				// particular, we need need to control over which characters and
				// numbers are in the domain.
				if (sym.type == elem::SYM) {
					d.get_sym(sym.e);
				}
			}
			// Get all the relations used in both queries
			set<rel_info> rels;
			for (const raw_term &rt : rr1.b[0]) rels.insert(get_relation_info(rt));
			for (const raw_term &rt : rr2.b[0]) rels.insert(get_relation_info(rt));
			// Now we need to get the largest superset of our canonical
			// database
			set<raw_term> superset;
			for (const rel_info &ri : rels) {
				vector<elem> tuple;
				product_iter(symbol_set, tuple, get<1>(ri),
					[&](const vector<elem> tuple) -> bool {
						vector<elem> nterm_e = { get<0>(ri), elem_openp };
						for(const elem &e : tuple) {
							nterm_e.push_back(e);
						}
						nterm_e.push_back(elem_closep);
						raw_term nterm(nterm_e);
						superset.insert(nterm);
						return true;
					});
			}
			// Remove the frozen negative subgoals
			for (const raw_term &rt : canonical_negative) superset.erase(rt);
			// Now need to through all the supersets of our canonical database
			// and check that they yield the frozen head.
			return power_iter(superset, canonical,
				[&](const set<raw_term> ext) -> bool {
					raw_prog test_prog(dict);
					test_prog.r.push_back(rr2);
					set<raw_term> res;
					tables::run_prog_wedb(ext, test_prog, d, opts, res);
					return res.find(subbed.h[0]) != res.end();
				});
		});

	if (contained) {
		o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
		return true;
	} else {
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
		return false;
	}
}

/*!
 * If rr1 and rr2 are both conjunctive queries with negation, check that
 * rr1 is contained by rr2. 
 * 
 * The implementation is based in the Levy-Sagiv test. 
 */
bool driver::o2_cqnc(const raw_rule &rr1, const raw_rule &rr2) {
	// Check that rules have correct format
	if (!(is_cqn(rr1) && is_cqn(rr2) &&
		get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0]))) return false;

	o::dbg() << "CQNC Testing if " << rr1 << " <= " << rr2 << endl;

	set<elem> vars;
	collect_vars(rr1, vars);
	vector<set<elem>> partition;

	// Do the Levy-Sagiv test
	bool contained = partition_iter(vars, partition,
		[&](const vector<set<elem>> &partition) -> bool {
			// Print the current partition
			o::dbg() << "Testing partition: ";
			for (const set<elem> &s : partition) {
				o::dbg() << "{";
				for (const elem &e : s) {
					o::dbg() << e << ", ";
				}
				o::dbg() << "}, ";
			}
			o::dbg() << endl;

			// Create new dictionary so that symbols created for these tests
			// do not affect final program
			dict_t d;

			// Map each variable to a fresh symbol according to the partition
			map<elem, elem> subs;
			for (const set<elem> &part : partition) {
				elem pvar = elem::fresh_sym(d);
				for (const elem &e : part) {
					subs[e] = pvar;
				}
			}
			raw_rule subbed = freeze_rule(rr1, subs, d);
			set<raw_term> canonical, canonical_negative;
			// Separate the positive and negative subgoals. Note the symbols
			// supplied to the subgoals.
			for (raw_term &rt : subbed.b[0]) {
				if (rt.neg) {
					rt.neg = false;
					canonical_negative.insert(rt);
					rt.neg = true;
				} else canonical.insert(rt);
			}
			// Print the canonical database
			o::dbg() << "Current canonical Database: ";
			for (const raw_term &rt : canonical) {
				o::dbg() << rt << ", ";
			}
			o::dbg() << endl;
			// Does canonical database make all the subgoals of subbed true?
			for (raw_term &rt : subbed.b[0]) {
				if (rt.neg) {
					// If the term in the rule is negated, we need to make sure
					// that it is not in the canonical database.
					rt.neg = false;
					if (canonical.find(rt) != canonical.end()) {
						o::dbg() << "Current canonical database causes its source query to be inconsistent."
							<< endl;
						return true;
					}
					rt.neg = true;
				}
			}
			// Collect the symbols/literals from the freeze map
			set<elem> symbol_set;
			for (const auto &[elm, sym] : subs) {
				symbol_set.insert(sym);
				// Finer control over elements in the universe is required to
				// make this algorithm work with unsafe negations. In
				// particular, we need need to control over which characters and
				// numbers are in the domain.
				if (sym.type == elem::SYM) {
					d.get_sym(sym.e);
				}
			}
			// Get all the relations used in both queries
			set<rel_info> rels;
			for (const raw_term &rt : rr1.b[0]) rels.insert(get_relation_info(rt));
			for (const raw_term &rt : rr2.b[0]) rels.insert(get_relation_info(rt));
			// Now we need to get the largest superset of our canonical
			// database
			set<raw_term> superset;
			for (const rel_info &ri : rels) {
				vector<elem> tuple;
				product_iter(symbol_set, tuple, get<1>(ri),
					[&](const vector<elem> tuple) -> bool {
						vector<elem> nterm_e = { get<0>(ri), elem_openp };
						for(const elem &e : tuple) {
							nterm_e.push_back(e);
						}
						nterm_e.push_back(elem_closep);
						raw_term nterm(nterm_e);
						superset.insert(nterm);
						return true;
					});
			}
			// Remove the frozen negative subgoals
			for (const raw_term &rt : canonical_negative) superset.erase(rt);
			// Now need to through all the supersets of our canonical database
			// and check that they yield the frozen head.
			return power_iter(superset, canonical,
				[&](const set<raw_term> ext) -> bool {
					raw_prog test_prog(dict);
					test_prog.r.push_back(rr2);
					set<raw_term> res;
					tables::run_prog_wedb(ext, test_prog, d, opts, res);
					return res.find(subbed.h[0]) != res.end();
				});
		});

	if (contained) {
		o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
		return true;
	} else {
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
		return false;
	}
}

/* Takes two DNF rules and returns true if the first is "smaller" than the
 * second. Smaller means less conjuncts in the body, and in the case of a tie
 * means less arguments in the head. */

bool rule_smaller(const raw_rule &rr2, const raw_rule &rr1) {
	if(rr1.b.size() == 1 && rr2.b.size() == 1) 
		return (rr1.b[0].size() == rr2.b[0].size())
			? rr1.h[0].e.size() > rr2.h[0].e.size()
			: rr1.b[0].size() > rr2.b[0].size();
	return rr1.b.size() > rr2.b.size();
}

/* If rr1 and rr2 are both conjunctive bodies, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that a valid substitution for rr1 can be
 * turned into a valid substitution for rr2. This function provides all
 * off them. */

bool driver::cbc(const raw_rule &rr1, raw_rule rr2,
		set<terms_hom> &homs) {
	// Get dictionary for generating fresh symbols
	dict_t d;

	if (is_cq(rr1) && is_cq(rr2)) {
		o::dbg() << "Searching for homomorphisms from " << rr2.b[0]
			<< " to " << rr1.b[0] << endl;
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		// Map from variables occuring in rr1 to frozen symbols
		map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);
		// Map from frozen symbols to variables occuring in rr1
		map<elem, elem> unfreeze_map;
		for (const auto &[k, v] : freeze_map) unfreeze_map[v] = k;
		// Build up the extensional database necessary to check homomorphism.
		set<raw_term> edb;
		// Map from term ids to terms in rr1
		map<elem, raw_term> term_map;
		int j = 0;
		// First put the frozen terms of rr1 into our containment program
		for (raw_term &rt : frozen_rr1.b[0]) {
			// Record the mapping from the term id to the raw_term it
			// represents
			elem term_id = elem::fresh_sym(d);
			term_map[term_id] = rr1.b[0][j++];
			// Mark our frozen term with an id so that we can trace the terms
			// involved in the homomorphism if it exists
			rt.e.insert(rt.e.begin() + 2, term_id);
			rt.calc_arity(nullptr);
			edb.insert(rt);
		}

		o::dbg() << "Canonical Database: " << edb << endl;

		// Build up the query that proves the existence of a homomorphism
		// Make a new head for rr2 that exports all the variables used in
		// its body + ids of the frozen terms it binds to
		set<elem> rr2_body_vars_set;
		collect_vars(rr2.b[0].begin(), rr2.b[0].end(), rr2_body_vars_set);
		vector<elem> rr2_new_head = { elem::fresh_temp_sym(d), elem_openp };
		rr2_new_head.insert(rr2_new_head.end(), rr2_body_vars_set.begin(),
			rr2_body_vars_set.end());
		// Prepend term id variables to rr2's body terms and export the term
		// ids through the head
		for(raw_term &rt : rr2.b[0]) {
			// This variable will bind to the term id of a frozen body term
			// used in the homomorphism
			elem term_id = elem::fresh_var(d);
			rt.e.insert(rt.e.begin() + 2, term_id);
			rt.calc_arity(nullptr);
			rr2_new_head.push_back(term_id);
		}
		rr2_new_head.push_back(elem_closep);
		// Put body and head together and make containment program
		rr2.h[0] = raw_term(rr2_new_head);
		raw_prog nrp(dict);
		nrp.r.push_back(rr2);

		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		set<raw_term> results;
		if (!tables::run_prog_wedb(edb, nrp, d, opts, results)) return false;
		for (const raw_term &res : results) {
			// If the result comes from the containment query (i.e. it is not
			// one of the frozen terms), then there is a homomorphism between
			// the bodies
			raw_term hd_src = rr2.h[0];
			if (res.e[0] == hd_src.e[0]) {
				var_subs var_map;
				set<raw_term> target_terms;
				// Now we want to express the homomorphism in terms of the
				// original (non-frozen) variables and terms of rr1.
				for (size_t i = 2; i < res.e.size() - 1; i++)
					// If current variable is a body var
					if (rr2_body_vars_set.find(hd_src.e[i]) != rr2_body_vars_set.end()) 
						// Then trace the original var through the unfreeze map
						var_map[hd_src.e[i]] = at_default(unfreeze_map, res.e[i], res.e[i]);
					else
						// Otherwise trace the original term through the term map
						target_terms.insert(term_map[res.e[i]]);
				homs.insert(make_pair(target_terms, var_map));
				// Print the homomorphism found
				o::dbg() << "Found homomorphism from " << rr2.b[0] << " to "
					<< target_terms << " under mapping {";
				for (auto &[k, v] : var_map) {
					o::dbg() << k << " -> " << v << ", ";
				}
				o::dbg() << "}" << endl;
			}
		}
		// If no results produced, then there is no homomorphism.
		return true;
	}
	return false;
}


/* Count the number of rules (including the given one) that derive facts
 * for the same relation that the given rule derives facts for. */

int_t driver::count_related_rules(const raw_rule &rr1, const raw_prog &rp) {
	int_t count = 0;
	for(const raw_rule &rr2 : rp.r)
		if(rr1.h[0].e[0] == rr2.h[0].e[0] &&
				rr1.h[0].e.size() == rr2.h[0].e.size())
			count++;
	return count;
}

/* Given a homomorphism (i.e. a pair comprising variable substitutions
 * and terms surjected onto) and the rule that a homomorphism maps into,
 * determine which variables of the domain would be needed to express
 * constraints in the codomain. */

void driver::compute_required_vars(const raw_rule &rr,
		const terms_hom &hom, set<elem> &orig_vars) {
	auto &[rts, vs] = hom;
	// Get all the terms used by the given rule.
	set<raw_term> aggregate(rr.h.begin(), rr.h.end());
	aggregate.insert(rr.b[0].begin(), rr.b[0].end());
	// Make a vector containing all terms used by the given rule that are
	// not in homomorphism target.
	vector<raw_term> diff(aggregate.size());
	auto it = set_difference(aggregate.begin(), aggregate.end(),
		rts.begin(), rts.end(), diff.begin());
	diff.resize(it - diff.begin());
	// Get variables used outside homomorphism target
	set<elem> diff_vars;
	collect_vars(diff.begin(), diff.end(), diff_vars);
	// Get variables used inside homomorphism target
	set<elem> rts_vars;
	collect_vars(rts.begin(), rts.end(), rts_vars);
	// Compute the variables of the homomorphism target that we need to
	// retain control of
	vector<elem> nonfree_vars(diff_vars.size());
	auto jt = set_intersection(diff_vars.begin(), diff_vars.end(),
		rts_vars.begin(), rts_vars.end(), nonfree_vars.begin());
	nonfree_vars.resize(jt - nonfree_vars.begin());
	// Trace these variables of the homomorphism target to the
	// homomorphism source.
	for (auto &[var, covar] : vs)
		if(find(nonfree_vars.begin(), nonfree_vars.end(), covar) !=
				nonfree_vars.end()) 
			orig_vars.insert(var);
}

/* Algorithm to factor the rules in a program using other rules.
 * Starting with the conjunctive rules with the biggest bodies, record
 * all the homomorphisms from this body into the bodies of other rules.
 * Afterwards, check if the head of this rule could be substituted
 * verbatim into the bodies of other rules, or whether a temporary
 * relation taking more arguments would be required. Afterwards,
 * replace the homomorphism targets with our chosen head. */

void driver::factor_rules(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	o::dbg() << "Factorizing rules ..." << endl;

	// Sort the rules so the biggest come first. Idea is that we want to
	// reduce total substitutions by doing the biggest factorizations
	// first. Also prioritizing rules with more arguments to reduce chance
	// that tmprel with more arguments is created.
	sort(rp.r.rbegin(), rp.r.rend(), rule_smaller);
	// The place where we temporarily store our temporary rules
	vector<raw_rule> pending_rules;
	// Go through the rules we want to try substituting into other
	for (raw_rule &rr2 : rp.r) {
		// Because we use a conjunctive homomorphism finding rule
		if (is_cq(rr2) && rr2.b[0].size() > 1) {
			// The variables of the current rule that we'd need to be able to
			// constrain/substitute into
			set<elem> needed_vars;
			set<tuple<raw_rule *, terms_hom>> agg;
			// Now let's look for rules that we can substitute the current
			// into
			for (raw_rule &rr1 : rp.r) {
				set<terms_hom> homs;
				// Find all the homomorphisms between outer and inner rule. This
				// way we can substitute the outer rule into the inner multiple
				// times.
				if (is_cq(rr1) && cbc(rr1, rr2, homs)) {
					for (const terms_hom &hom : homs) {
						auto &[target_terms, var_map] = hom;
						// Record only those homomorphisms where the target is at
						// least as big as the source for there is no point in
						// replacing a group of terms with a rule utilizing a bigger
						// group.
						if (target_terms.size() >= rr2.b[0].size()) {
							agg.insert(make_tuple(&rr1, hom));
							// If we were to substitute the target group of terms with
							// a single head, what arguments would we need to pass to
							// it?
							compute_required_vars(rr1, hom, needed_vars);
						}
					}
				}
			}

			// Now we need to figure out if we should create a temporary
			// relation containing body of current rule or whether we can just
			// use it directly. This depends on whether the head exports
			// enough variables.
			elem target_rel;
			vector<elem> target_args;
			set<elem> exported_vars;
			collect_vars(rr2.h[0], exported_vars);
			// Note whether we have created a temporary relation. Important
			// because we make the current rule depend on the temporary
			// relation in this case.
			bool tmp_rel =
				!((exported_vars == needed_vars && count_related_rules(rr2, rp) == 1) ||
					agg.size() == 1);

			if (tmp_rel) {
				// Variables are not exactly what is required. So make relation
				// exporting required variables and note argument order.
				target_rel = elem::fresh_temp_sym(d);
				target_args.assign(needed_vars.begin(), needed_vars.end());
				pending_rules.push_back(raw_rule(raw_term(target_rel, target_args), rr2.b[0]));
			} else {
				// The variables exported by current rule are exactly what is
				// needed by all homomorphisms from current body
				target_rel = rr2.h[0].e[0];
				for (size_t i = 2; i < rr2.h[0].e.size() - 1; i++) target_args.push_back(rr2.h[0].e[i]);
			}

			// Now we go through all the homomorphisms and try to apply
			// substitutions to their targets
			for (auto &[rr1, hom] : agg) {
				// If no temporary relation was created, then don't touch the
				// outer rule as its definition is irreducible.
				if (!tmp_rel && rr1 == &rr2) continue;
				auto &[rts, vs] = hom;
				set<raw_term> rr1_set(rr1->b[0].begin(), rr1->b[0].end());
				// If the target rule still includes the homomorphism target,
				// then ... . Note that this may not be the case as the targets
				// of several homomorphisms could overlap.
				if (includes(rr1_set.begin(), rr1_set.end(), rts.begin(),
						rts.end())) {
					// Remove the homomorphism target from the target rule
					auto it = set_difference(rr1_set.begin(), rr1_set.end(),
						rts.begin(), rts.end(), rr1->b[0].begin());
					rr1->b[0].resize(it - rr1->b[0].begin());
					// And place our chosen head with localized arguments.
					vector<elem> subbed_args;
					for (const elem &e : target_args)
						// If the current parameter of the outer rule is a constant,
						// then just place it in our new term verbatim
						subbed_args.push_back(at_default(vs, e, e));
					rr1->b[0].push_back(raw_term(target_rel, subbed_args));
				}
			}
		}
	}
	// Now add the pending rules. Done here to prevent movement of rules
	// during potential vector resizing.
	for (const raw_rule &rr : pending_rules) {
		rp.r.push_back(rr);
		o::dbg() << "New Factor Created: " << rr << endl;
	}
}

void driver::o1_transform_bin(raw_prog& p) {
	transform_bin(p);
}

void driver::o2_subsume_queries_cqc(raw_prog &rp) {
	subsume_queries(rp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return o2_cqc(rr1, rr2);});
}

void driver::o2_subsume_queries_cqnc(raw_prog &rp) {
	subsume_queries(rp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return o2_cqnc(rr1, rr2);});
}
