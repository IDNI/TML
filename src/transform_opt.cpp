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

#include <optional>
#include <functional>

#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt.h"

using namespace std;

cost_function exp_in_heads = [](mutated_prog &mp) {
	auto rs = mp.current.r;
	size_t c = 0.0;
	for (auto it = rs.begin(); it != rs.end(); ++it) {
		c += (*it).h.size() * (*it).b.size();
	}
	return c;
};

void mutated_prog::operator()(mutation &m) {
	// apply the mutation to the current mutated_prog
	m(*this);
}

//mutated_prog *mutated_prog::operator--() {
//	return previous;
//}

/*!
 * Collapse all valid raw rules into a vector.
 */ 
/*vector<raw_rule>  mutated_prog::get_rules() {
	vector<raw_rule> all;
	if (!previous) {
		all.insert(all.end(), current.r.begin(), current.r.end());
		all.insert(all.end(), original.get().r.begin(), original.get().r.end());
		for (auto r: deletions) {
			auto i = find(all.begin(), all.end(), *r);
			if (i != all.end()) all.erase(i);
		}
		return all;
	}
	// get previous rules
	auto v = previous->get_rules();
	all.insert(all.end(), v.begin(), v.end());
	// remove current deletions
	for (auto r: deletions) {
		auto i = find(all.begin(), all.end(), *r);
		if (i != all.end()) all.erase(i);
	}
	// add current rules
	all.insert(all.end(), current.r.begin(), current.r.end());
	return all;
}*/

/*raw_prog  mutated_prog::to_raw_program() {
	if (!previous) {
		raw_prog new_raw_prog(original.get().dict);
		new_raw_prog.merge(original.get());
		new_raw_prog.merge(current);
		// remove current deletions
		for (auto &r: deletions) {
			auto i = find(new_raw_prog.r.begin(), new_raw_prog.r.end(), *r);
			if (i != new_raw_prog.r.end()) new_raw_prog.r.erase(i);
		}
		return new_raw_prog;
	}
	raw_prog new_raw_prog = previous->to_raw_program();
	new_raw_prog.merge(current);
	// remove current deletions
	for (auto &r: deletions) {
		auto i = find(new_raw_prog.r.begin(), new_raw_prog.r.end(), *r);
		if (i != new_raw_prog.r.end()) new_raw_prog.r.erase(i);
	}
	return new_raw_prog;
}*/

bool best_solution::bound(mutated_prog &p) {
	size_t cost = func_(p);
	if (cost < cost_) {
		cost_ = cost;
		best_[cost] = std::make_shared<mutated_prog>(p); // = p;
		return true;
	}
	return false;
}

raw_prog best_solution::solution() {
	return best_.begin().operator*().second.get()->current;
}

/*!
 * Optimize a mutated program
 */
vector<std::shared_ptr<mutation>> get_optimizations(mutated_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<mutation>>  optimizations;
	for(brancher brancher: branchers) {
		auto proposed = brancher(mutated);
		optimizations.insert(optimizations.end(), proposed.begin(), proposed.end());
	}
	return optimizations;
}

void optimize(mutated_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<mutation>>  optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current mutation and try to optimize again if needed
	for (auto it = optimizations.begin(); it != optimizations.end(); ++it) {
		(*it).get()->operator()(mutated);
	}
}

void optimize(mutated_prog& mutated, bounder& bounder, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<mutation>>  optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current mutation and try to optimize again if needed
	powerset_range<std::shared_ptr<mutation>> subsets(optimizations);
	for (auto it = ++subsets.begin(); it != subsets.end(); ++it) {
		mutated_prog new_mutated(mutated);
		vector<std::shared_ptr<mutation>> v = *it;
		for (auto mt = v.begin(); mt != v.end(); ++mt) (*mt).get()->operator()(new_mutated);
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
	mutated_prog mutated {program};
	o::dbg() << "Applying begin optimizations ..." << endl << endl;
	optimize(mutated, plan.begin); 
	plan.bndr.bound(mutated);
	o::dbg() << "Applying loop optimizations ..." << endl << endl;
	optimize(mutated, plan.bndr, plan.loop);
	// o::dbg() << "Applying end optimizations ..." << endl << endl;
	// mutated_prog loop{plan.bndr.solution()};
	// optimize(loop, plan.end);
	// plan.bndr.bound(mutated);
	return plan.bndr.solution();
}

raw_prog optimize(raw_prog& program, bounder& bounder, vector<brancher>& branchers) {
	// the first mutated program just contain the original program as additions.
	mutated_prog mutated {program};
	optimize(mutated, bounder, branchers);
	return bounder.solution();
}

struct mutation_add_rule : public virtual mutation  {
	raw_rule &rr;

	mutation_add_rule(raw_rule &r) : rr(r) {}

	bool const operator()(mutated_prog &mp) const override {
		mp.current.r.insert(mp.current.r.end(), rr);
		return true;
	}
};

struct mutation_add_del_rule : public virtual mutation  {
	raw_rule del_;
	raw_rule add_;

	mutation_add_del_rule(raw_rule del, raw_rule add) : del_(del), add_(add) {}

	bool const operator()(mutated_prog &mp) const override {
		mp.current.r.resize(mp.current.r.size() +1);
		mp.current.r.push_back(add_);
		remove(mp.current.r.begin(), mp.current.r.end(), del_);
		return true;
	}
};

struct mutation_remove_rule : public virtual mutation  {
	raw_rule &rr;

	mutation_remove_rule(raw_rule &r) : rr(r) {}

	bool const operator()(mutated_prog &mp) const override {
		remove(mp.current.r.begin(), mp.current.r.end(), rr);
		return true;
	}
};

/*! Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. 
 */
template<typename F>
std::vector<std::shared_ptr<mutation>> driver::brancher_subsume_queries(mutated_prog &mp /*rp*/, const F &f) {
	to_dnf(mp.current);
	split_heads(mp.current);
	std::vector<std::shared_ptr<mutation>> mutations;
	vector<raw_rule> reduced;
	for (raw_rule &rr : mp.current.r) {
		bool subsumed = false;
		for (auto nrr = reduced.begin(); nrr != reduced.end();) {
			if (f(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				mutation_add_del_rule del_add(rr, *nrr);
				mutations.push_back(std::make_shared<mutation_add_del_rule>(del_add));
				//mutations.push_back(add), mutations.push_back(del);
				subsumed = true;
				break;
			} else if (f(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				reduced.erase(nrr);
				// remove the subsumed rule and add the current rule
				mutation_remove_rule rem(*nrr);
				//	mutations.push_back(rem);
				mutations.push_back(std::make_shared<mutation_remove_rule>(rem));

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

std::vector<std::shared_ptr<mutation>> driver::brancher_subsume_queries_cqc(mutated_prog &mp) {
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqc(rr1, rr2);});
}

std::vector<std::shared_ptr<mutation>> driver::brancher_subsume_queries_cqnc(mutated_prog &mp) {
	return brancher_subsume_queries(mp,
		[this](const raw_rule &rr1, const raw_rule &rr2)
			{return cqnc(rr1, rr2);});
}

struct mutation_to_dnf : public virtual mutation  {
	driver &drvr;

	mutation_to_dnf(driver &d) : drvr(d) {}

	bool const operator()(mutated_prog &mp) const override {
		o::dbg() << "Converting to DNF format ..." << endl << endl;
//		drvr.to_dnf(mp.previous ? mp.current : mp.original.get());
		drvr.to_dnf(mp.current);
		o::dbg() << "DNF Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<mutation>> driver::brancher_to_dnf(mutated_prog &mp) {
	vector<std::shared_ptr<mutation>> mutations;
	mutation_to_dnf m(*this);
	mutations.push_back(std::make_shared<mutation_to_dnf>(m));
	return mutations; 
}

struct mutation_to_split_heads : public virtual mutation  {
	driver &drvr;

	mutation_to_split_heads(driver &d) : drvr(d) {}

	bool const operator()(mutated_prog &mp) const override {
		o::dbg() << "Splitting heads ..." << endl;
		drvr.split_heads(mp.current);
//		drvr.split_heads(mp.current);
		o::dbg() << "Binary Program:" << endl << mp.current << endl;
		return false;
	}
};

vector<std::shared_ptr<mutation>> driver::brancher_split_heads(mutated_prog &mp) {
	vector<std::shared_ptr<mutation>> mutations;
	mutation_to_split_heads m(*this);
	mutations.push_back(std::make_shared<mutation_to_split_heads>(m));
	return mutations;
}

struct mutation_eliminate_dead_variables : public virtual mutation  {
	driver &drvr;

	mutation_eliminate_dead_variables(driver &d) : drvr(d) {}

	bool const operator()(mutated_prog &mp) const override {
		o::dbg() << "Eliminating dead variables ..." << endl << endl;
		drvr.eliminate_dead_variables(mp.current);
//		drvr.eliminate_dead_variables(mp.current);
		o::dbg() << "Stripped TML Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<mutation>> driver::brancher_eliminate_dead_variables(mutated_prog &mp) {
	vector<std::shared_ptr<mutation>> mutations;
	mutation_eliminate_dead_variables m(*this);
	mutations.push_back(std::make_shared<mutation_eliminate_dead_variables>(m));
	return mutations;
}

struct mutation_export_outer_quantifiers : public virtual mutation  {
	driver &drvr;

	mutation_export_outer_quantifiers(driver &d) : drvr(d) {}

	bool const operator()(mutated_prog &mp) const override {
		o::dbg() << "Exporting Outer Quantifiers ..." << endl << endl;
		drvr.export_outer_quantifiers(mp.current);
		o::dbg() << "Reduced Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<mutation>> driver::brancher_export_outer_quantifiers(mutated_prog &mp) {
	// Trimmed existentials are a precondition to program optimizations
	vector<std::shared_ptr<mutation>> mutations;
	mutation_export_outer_quantifiers m(*this);
	mutations.push_back(std::make_shared<mutation_export_outer_quantifiers>(m));
	return mutations;
}

struct mutation_split_bodies : public virtual mutation  {
	driver &drvr;

	mutation_split_bodies(driver &d) : drvr(d) {}

	bool const operator()(mutated_prog &mp) const override {
		o::dbg() << "Splitting bodies ..." << endl;
		drvr.transform_bin(mp.current);
		o::dbg() << "Binary Program:" << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<mutation>> driver::brancher_split_bodies(mutated_prog &mp) {
	vector<std::shared_ptr<mutation>> mutations;
	mutation_split_bodies m(*this);
	mutations.push_back(std::make_shared<mutation_split_bodies>(m));
	return mutations;
}

optimization_plan::optimization_plan(bounder &b) : bndr(b) {}