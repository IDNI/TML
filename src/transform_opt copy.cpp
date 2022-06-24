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

#include <optional>
#include <functional>

#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt.h"

using namespace std;

cost_function constant_cost_function = [](mutated_prog &mp) { return 1.0; };

cost_function exp_in_heads = [](mutated_prog &mp) {
	auto r = (mp.get_rules());
	double c = 0.0;
	for (auto &r: mp.get_rules()) {
		c += r.h.size() + log(r.b.size());
	}
	return c;
};


// starting node of the mutated progs log
mutated_prog::mutated_prog(){}

// starting node of the mutated progs log
mutated_prog::mutated_prog(raw_prog *p) : current(p) {}

// link to previous mutated prog
mutated_prog::mutated_prog(mutated_prog *m) : previous(m) {}

void mutated_prog::operator()(mutation &m) {
	// apply the mutation to the current mutated_prog
	m(*this);
}

mutated_prog *mutated_prog::operator--() {
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
	for (auto r: deletions) {
		auto i = find(all.begin(), all.end(), *r);
		if (i != all.end()) all.erase(i);
	}
	// add current rules
	all.insert(all.end(), current->r.begin(), current->r.end());
	return all;
}

raw_prog  mutated_prog::to_raw_program() {
	if (!previous) {
		// remove current deletions
		for (auto &r: deletions) {
			auto i = find(current->r.begin(), current->r.end(), *r);
			if (i != current->r.end()) current->r.erase(i);
		}
		return *current;
	}
	auto p = (*previous).to_raw_program();
	for (auto &r: deletions) {
		auto i = find(current->r.begin(), current->r.end(), *r);
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
vector<mutation*> get_optimizations(mutated_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<mutation*> optimizations;
	for(brancher brancher: branchers) {
		auto proposed = brancher(mutated);
		optimizations.insert(optimizations.end(), proposed.begin(), proposed.end());
	}
	return optimizations;
}

void optimize(mutated_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<mutation*> optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current mutation and try to optimize again if needed
	for (auto it = optimizations.begin(); it != optimizations.end(); ++it) {
		(**it)(mutated);
	}
}

void optimize(mutated_prog& mutated, bounder& bounder, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<mutation*> optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current mutation and try to optimize again if needed
	powerset_range<mutation*> subsets(optimizations);
	for (auto it = subsets.begin(); it != subsets.end(); ++it) {
		mutated_prog new_mutated(mutated);
		for (auto mt = (*it).begin(); mt != (*it).end(); ++mt) (**mt)(new_mutated);
		if (bounder.bound(new_mutated)) {
			optimize(new_mutated, bounder, branchers);
		}
	}
}

/*!
 * Optimize a raw program
 */
raw_prog optimize(raw_prog &program, optimization_plan &plan) {
	// the first mutated program just contain the original program as additions.
	mutated_prog mutated {&program};
	optimize(mutated, plan.begin); 
	plan.bndr.bound(mutated);
	optimize(mutated, plan.bndr, plan.loop);
	optimize(mutated, plan.end);
	plan.bndr.bound(mutated);
	return plan.bndr.solution();
}

raw_prog optimize(raw_prog& program, bounder& bounder, vector<brancher>& branchers) {
	// the first mutated program just contain the original program as additions.
	mutated_prog mutated {&program};
	optimize(mutated, bounder, branchers);
	return bounder.solution();
}

/*!
 * Minimizes the queries as much as posible.
 */
template<typename F>
vector<mutation*> brancher_minimize_queries(mutated_prog &mutated, const F &f) {
	vector<mutation*> mutations;
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
	mutation m = [minimized, deletions](mutated_prog &mp) {
		mp.current->r.insert(mp.current->r.end(), minimized.begin(), minimized.end());
		mp.deletions.insert(mp.deletions.end(), deletions.begin(), deletions.end());
	};
	mutations.push_back(&m);
	return mutations;
}

/*! Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. 
 */
template<typename F>
vector<mutation*> brancher_subsume_queries(mutated_prog &mp /*rp*/, const F &f) {
	vector<mutation*> mutations;
	vector<raw_rule> reduced;
	for (raw_rule &rr : mp.get_rules()) {
		bool subsumed = false;
		for (auto nrr = reduced.begin(); nrr != reduced.end();) {
			if (f(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				mutation l = [rr, nrr](mutated_prog &m) {
					m.current->r.insert(m.current->r.end(), rr);
					m.deletions.insert(m.deletions.end(), &(*nrr));
					return true;
				};
				mutations.push_back(&l);
				subsumed = true;
				break;
			} else if (f(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				reduced.erase(nrr);
				// remove the subsumed rule and add the current rule
				mutation l = [nrr](mutated_prog &m) {
					remove(m.current->r.begin(), m.current->r.end(), *nrr);
					return true;
				};
				mutations.push_back(&l);
			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if (!subsumed) reduced.push_back(rr);
	}
	return mutations;
}

#ifdef WITH_Z3
vector<mutation*> driver::brancher_subsume_queries_z3(mutated_prog &mp) {
	const auto &[int_bit_len, universe_bit_len] = prog_bit_len(mp.current);
	z3_context z3_ctx(int_bit_len, universe_bit_len);
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return check_qc_z3(rr1, rr2, z3_ctx);});
}
#endif

vector<mutation*> driver::brancher_subsume_queries_cqc(mutated_prog &mp) {
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqc(rr1, rr2);});
}

vector<mutation*> driver::brancher_subsume_queries_cqnc(mutated_prog &mp) {
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqnc(rr1, rr2);});
}


struct test_mutation : public mutation  {
	driver &drvr;

	test_mutation(driver &d) : drvr(d) {}

	bool operator()(mutated_prog &mp) {
		// do something
		return true;
	}
};

vector<mutation> driver::test(mutated_prog& mp) {
	vector<mutation> mutations;
	test_mutation tm(*this);
	mutations.push_back(tm);
	return mutations;
}

vector<mutation*> driver::brancher_to_dnf(mutated_prog &mp) {
	vector<mutation*> mutations;
	mutation l = [this](mutated_prog &p) {
		to_dnf(*(p.current));
		return true;
	};
	mutations.push_back(&l);
	return mutations;
}

vector<mutation*> driver::brancher_split_heads(mutated_prog &mp) {
	vector<mutation*> mutations;
	mutation l = [this](mutated_prog &p) {
		split_heads(*(p.current));
		return true;
	};
	mutations.push_back(&l);
	return mutations;
}

vector<mutation*> driver::brancher_eliminate_dead_variables(mutated_prog &mp) {
	vector<mutation*> mutations;
	mutation l = [this](mutated_prog &p) {
		eliminate_dead_variables(*(p.current));
		return true;
	};
	mutations.push_back(&l);
	return mutations;
}

vector<mutation*> driver::brancher_export_outer_quantifiers(mutated_prog &mp) {
	vector<mutation*> mutations;
	mutation l = [this](mutated_prog &p) {
		export_outer_quantifiers(*(p.current));
		return true;
	};
	mutations.push_back(&l);
	return mutations;
}

vector<mutation*> driver::brancher_split_bodies(mutated_prog &mp) {
	vector<mutation*> mutations;
	mutation l = [this](mutated_prog &p) {
		transform_bin(*(p.current));
		return true;
	};
	mutations.push_back(&l);
	return mutations;
}

vector<mutation*> driver::brancher_square_program(mutated_prog &mp) {
	vector<mutation*> mutations;
	mutation l = [this](mutated_prog &p) {
		square_program(*(p.current));
		return true;
	};
	mutations.push_back(&l);
	return mutations;
}

optimization_plan::optimization_plan(bounder &b) : bndr(b) {}