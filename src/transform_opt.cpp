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

#include "driver.h"
#include "err.h"
#include "iterators.h"
// #include "generators.h"
#include "transform_opt.h"

using namespace std;

cost_function exp_in_heads = [](changed_prog &mp) {
	auto rs = mp.current;
	size_t c = 0.0;
	for (auto it = rs.begin(); it != rs.end(); ++it) {
		// TODO properly define this cost function
		c += (*it).size();
	}
	return c;
};

void changed_prog::operator()(change &m) {
	// apply the change to the current changed_prog
	m(*this);
}

bool best_solution::bound(changed_prog &p) {
	size_t cost = func_(p);
	if (cost < cost_) {
		cost_ = cost;
		best_ = std::make_shared<changed_prog>(p);
		return true;
	}
	return false;
}

flat_prog best_solution::solution() {
	return best_.get()->current;
}

#ifdef DELETE_ME
/* 
 * Squaring program 
 *
 */


/* If the given element is a variable, rename it using the relevant
 * mapping. If the mapping does not exist, then create a new one. */

elem rename_variables(const elem &e, map<elem, elem> &renames,
		const function<elem (const elem &)> &gen) {
	if(e.type == elem::VAR) {
		if(auto it = renames.find(e); it != renames.end()) {
			return it->second;
		} else {
			return renames[e] = gen(e);
		}
	} else return e;
}

/* Rename all the variables in the given formula tree using the given
 * mappings. Where the mappings do not exist, create them. Note that
 * variables introduced inside quantifiers are treated as distinct. Note
 * also that the mappings made for variables introduced inside
 * quantifiers are not exported. */

void rename_variables(raw_form_tree &t, map<elem, elem> &renames,
		const function<elem (const elem &)> &gen) {
	switch(t.type) {
		case elem::NONE: {
			for(elem &e : t.rt->e) e = rename_variables(e, renames, gen);
			break;
		} case elem::NOT: {
			rename_variables(*t.l, renames, gen);
			break;
		} case elem::ALT: case elem::AND: case elem::IMPLIES:
				case elem::COIMPLIES: {
			rename_variables(*t.l, renames, gen);
			rename_variables(*t.r, renames, gen);
			break;
		} case elem::FORALL: case elem::EXISTS: case elem::UNIQUE: {
			// The variable that is being mapped to something else
			const elem ovar = *t.l->el;
			// Get what that variable maps to in the outer scope
			const auto &ivar = renames.find(ovar);
			const optional<elem> pvar = ivar == renames.end() ? nullopt : make_optional(ivar->second);
			// Temporarily replace the outer scope mapping with new inner one
			*t.l->el = renames[ovar] = gen(ovar);
			// Rename body using inner scope mapping
			rename_variables(*t.r, renames, gen);
			// Now restore the (possibly non-existent) outer scope mapping
			if(pvar) renames[ovar] = *pvar; else renames.erase(ovar);
			break;
		} default:
			assert(false); //should never reach here
	}
}

/* Useful when copying formula trees whilst trying to ensure that none of its
 * variables are accidentally captured by the context into which its being
 * inserted. */

function<elem (const elem &)> gen_fresh_var(dict_t &d) {
	return [&d](const elem &) {return elem::fresh_var(d);};
}

/* Useful when copying formula tree whilst only modifying a limited set of
 * variables. */

elem gen_id_var(const elem &var) {
	return var;
}

/* Expand the given term using the given rule whose head unifies with
 * it. Literally returns the rule's body with its variables replaced by
 * the arguments of the given term or fresh variables. Fresh variables
 * are used so that the produced formula tree can be grafted in
 * anywhere. */

raw_form_tree driver::expand_term(const raw_term &use,
		const raw_rule &def) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	const raw_term &head = def.h[0];
	// Where all the mappings for the substitution will be stored
	map<elem, elem> renames;
	// Let's try to reduce the number of equality constraints required
	// by substituting some of the correct variables in the first place.
	for(size_t i = 2; i < head.e.size() - 1; i++) {
		if(head.e[i].type == elem::VAR) {
			renames[head.e[i]] = use.e[i];
		}
	}
	// Deep copy the rule's body because the in-place renaming required
	// for this expansion should not affect the original
	raw_form_tree subst = *def.get_prft();
	rename_variables(subst, renames, gen_fresh_var(d));
	// Take care to existentially quantify the non-exported variables of this
	// formula in case it is inserted into a negative context
	for(const auto &[ovar, nvar] : renames) {
		if(find(use.e.begin() + 2, use.e.end() - 1, nvar) == use.e.end() - 1) {
			subst = raw_form_tree(elem::EXISTS,
				make_shared<raw_form_tree>(nvar),
				make_shared<raw_form_tree>(subst));
		}
	}
	// Append remaining equality constraints to the renamed tree to link
	// the logic back to its context
	for(size_t i = 2; i < head.e.size() - 1; i++) {
		// Add equality constraint only if it has not already been captured
		// in the substitution choice.
		elem new_name = rename_variables(head.e[i], renames, gen_fresh_var(d));
		if(new_name != use.e[i]) {
			subst = raw_form_tree(elem::AND,
				make_shared<raw_form_tree>(subst),
				make_shared<raw_form_tree>(raw_term(raw_term::EQ,
					{ use.e[i], elem(elem::EQ), new_name })));
		}
	}
	return subst;
}

/* Produces a program where executing a single step is equivalent to
 * executing two steps of the original program. This is achieved through
 * inlining where each body term is replaced by the disjunction of the
 * bodies of the relation that it refers to. For those facts not
 * computed in the previous step, it is enough to check that they were
 * derived to steps ago and were not deleted in the previous step. */

void driver::square_program(raw_prog &rp) {
	// Partition the rules by relations
	typedef set<raw_rule> relation;
	map<rel_info, relation> rels;
	// Separate the program rules according to the relation they belong
	// to and their sign. This will simplify lookups during inlining.
	for(const raw_rule &rr : rp.r)
		if(!rr.is_fact() && !rr.is_goal())
			rels[get_relation_info(rr.h[0])].insert(rr);

	// The place where we will construct the squared program
	vector<raw_rule> squared_prog;
	for(const raw_rule &rr : rp.r) {
		if(rr.is_fact() || rr.is_goal()) {
			// Leave facts alone as they are not part of the function
			squared_prog.push_back(rr);
		} else {
			// Deep copy so that we can inline out of place. Future terms/
			// rules may need the original body of this rule
			raw_form_tree nprft = *rr.get_prft();
			// Iterate through tree looking for terms
			postfold_tree(nprft, monostate {},
				[&](raw_form_tree &t, monostate acc) -> monostate {
					if(t.type == elem::NONE && t.rt->extype == raw_term::REL) {
						// Replace term according to following rule:
						// term -> (term && ~del1body && ... && ~delNbody) ||
						// ins1body || ... || insMbody
						raw_term &rt = *t.rt;
						// Inner conjunction to handle case where fact was derived
						// before the last step. We just need to make sure that it
						// was not deleted in the last step.
						optional<raw_form_tree> subst;
						// Outer disjunction to handle the case where fact derived
						// exactly in the last step.
						for(const raw_rule &rr : rels[get_relation_info(rt)])
							subst = !subst ? expand_term(rt, rr) :
								raw_form_tree(elem::ALT,
									make_shared<raw_form_tree>(*subst),
									make_shared<raw_form_tree>(expand_term(rt, rr)));
						// We can replace the raw_term now that we no longer need it
						if(subst) t = *subst;
					}
					// Just a formality. Nothing is being accumulated.
					return acc; });
			squared_prog.push_back(raw_rule(rr.h[0], nprft));
		}
	}
	rp.r = squared_prog;
}
#endif // DELETE_ME

#ifndef WORK_IN_PROGRESS

using flat_rule = vector<term>;
using rel_arity = tuple<int_t, size_t>;
using rule_index = map<rel_arity, set<flat_rule>>; // TODO change to map<pair<int_t, int_t>, set<term_rule>> 
using unification = map<int_t, int_t>;

struct squaring_context {
	reference_wrapper<dict_t> dict;
	reference_wrapper<rule_index> index;
};

/* Get relation info in a way suitable for be used as key. */
rel_arity get_rel_info(const term &t) {
	return make_tuple(t[0], t.size());
}

rel_arity get_rel_info(const vector<term> &t) {
	return get_rel_info(t[0]);
}

/* Constructs a map with head/body information. In our case, the body is the 
 * first element of the vector of terms and the body the remaining terms. */
rule_index index_rules(const flat_prog &fp) {
	rule_index c;
	for (auto const &t: fp) 
		if (c.contains(get_rel_info(t))) c[get_rel_info(t)].insert(t);
		else c[get_rel_info(t)] = set<flat_rule> {t};
	return c;
}

/* Returns true if the vector of terms correspond to a fact, false otherwise. */
bool is_fact(const flat_rule &r) {
	// only one term and is not a goal
	return r.size() == 1 && !r[0].goal;
}

/* Returns true if the vector of terms correspond to a goal, false otherwise. */
bool is_goal(const flat_rule &r) {
	// TODO consider remove defensive programming
	// non empty and its a goal
	return !r.empty() && r[0].goal;
}

/* Compute the unification of two terms. */
unification unify(const term &t1, const term &t2) {
	unification nf;
	for (size_t i= 0; i != t1.size(); ++i) 
		if (nf.contains(t2[i]) && t2[i] != t1[i]) return unification();
		else nf[t2[i]] = t1[i];
	return nf;
}

flat_rule apply_unification(const unification &nf, flat_rule &r) {
	flat_rule n(r); 
	for (auto t: n) for( size_t i = 1; i != t.size(); ++i) 
		if (nf.contains(t[i])) t[i] = nf.at(t[i]);
	return n;
}

/* Returns the squaring of a term using a given rule. When considering negations 
 * we may return a set<vector<term>>. */
flat_rule square_term(const term &t, flat_rule &r) {
	/* TODO something using distributive law: if (t.neg) {...} */;
	auto nf = unify(t, r[0]); /* TODO something if no unification is possible */
	return apply_unification(nf, r);
}

/* Copmpute the last var used in the given rule. */
int_t get_last_var(const flat_rule &r) {
	int_t lst = 0;
	for (auto &t: r) for (auto i: t) lst = (i < lst) ? i : lst;
	return lst;
}

/* Renames all variables of a rule. */
flat_rule rename_rule_vars(const flat_rule &r, int_t& lv) {
	flat_rule rr(r);
	map<int_t, int_t> sbs;
	for (auto &t: rr) for (auto i = 0; i != t.size(); ++i)
		if (!sbs.contains(t[i]) && t[i] < 0) sbs[t[i]] = --lv, t[i] = sbs[t[i]];
	return rr;
}

/* Returns the squaring of a term.  */
set<flat_rule> square_term(const term &t, const rule_index &ndx, int_t& lv) {
	set<flat_rule> sqr;
	for (auto &r: ndx.at(get_rel_info(t))) {
		auto rnmd = rename_rule_vars(r, lv);
		sqr.insert(square_term(t, rnmd));
	}
	return sqr;
}

set<flat_rule> shuffle(const set<flat_rule> &hs, const set<flat_rule> &ts) {
	set<flat_rule> shffl;
	for (auto h: hs) for (auto const& t: ts) {
		flat_rule n(h.begin(), h.end());
		for (auto e: t) n.emplace_back(e);
		shffl.emplace(n);
	}
	return shffl;
}

/* Returns the squaring of a rule  */
template<typename iterator>
set<flat_rule> square_rule_tail(iterator &b, iterator &e, const rule_index &ndx, int_t& lv) {
	auto hs = square_term(*b, ndx, lv); 
	if (distance(b, e) > 1) {
		auto ts = square_rule_tail(++b, e, ndx, lv);
		return shuffle(hs, ts);
	} else return hs;
}

/* Returns the squaring of a rule. As square_program automatically 
 * deals with facts and goals, we could assume that the body is not empty. */
set<flat_rule> square_rule(flat_rule &r, const rule_index &ndx) {
	auto lv = get_last_var(r); auto b = r.begin(); auto e = r.end();
	set<flat_rule> head{{*b}};
	auto sqr_tails = square_rule_tail(++b, e, ndx, lv);
	return shuffle(head, sqr_tails);
}

/*! Produces a program where executing a single step is equivalent to
 * executing two steps of the original program. This is achieved through
 * inlining where each body term is replaced by the disjunction of the
 * bodies of the relation that it refers to. For those facts not
 * computed in the previous step, it is enough to check that they were
 * derived to steps ago and were not deleted in the previous step. */
flat_prog square_program(const flat_prog &fp) {
	// new flat_prog holding the squaring of fp
	flat_prog sqr;
	// cache info for speed up the squaring holding a map between heads
	// and bodies
	auto ndx = index_rules(fp);
	for (auto r: fp) {
		if(is_fact(r) || is_goal(r)) sqr.insert(r);
		// TODO review if we need something else with the head
		else {
			auto nr = square_rule(r, ndx);
			sqr.insert(nr.begin(), nr.end()); 
		}
	}
	return sqr;
}

/* Minimize the rule using CQC */
flat_rule minimize_rule(flat_rule $fp) {
	flat_rule mnmzd;
	// do minimization
	return mnmzd;
}

/* Returns all the possible splittings of the rule */
set<pair<flat_rule, flat_rule>> split_rule(flat_rule $fp) {
	set<pair<flat_rule, flat_rule>> splt;
	// do splitting
	return splt;
}

#endif // WORK_IN_PROGRESS

#ifdef CHANGE_ME
/*!
 * Optimize a mutated program
 */
vector<std::shared_ptr<change>> get_optimizations(changed_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<change>>  optimizations;
	for(brancher brancher: branchers) {
		auto proposed = brancher(mutated);
		optimizations.insert(optimizations.end(), proposed.begin(), proposed.end());
	}
	return optimizations;
}

/*! Entry point for optimization process. */

void optimize(flat_prog fp) {
	changed_prog cp(fp);
	best_solution bs(exp_in_heads, fp); 

	if(int_t iter_num = opts.get_int("O3")) {
	// Trimmed existentials are a precondition to program optimizations
	o::dbg() << "Removing Redundant Quantifiers ..." << endl << endl;

	// remove call to pdatalog_transform
	pdatalog_transform(rp, [&](raw_prog &rp) {
		o::dbg() << "P-DATALOG Pre-Transformation:" << endl << endl << rp << endl;
		split_heads(rp);
		// Alternately square and simplify the program iter_num times
		for(int_t i = 0; i < iter_num; i++) {
			o::dbg() << "Squaring Program ..." << endl << endl;
			square_program(rp);
			o::dbg() << "Squared Program: " << endl << endl << rp << endl;
		}
		o::dbg() << "P-DATALOG Post-Transformation:" << endl << endl << rp << endl;
	});

	if(opts.enabled("O1") || opts.enabled("O2")) {
		flat_prog fp;
		changed_prog mp(fp);
		plan begin(bs);
		flat_prog optimized(fp);
		if (!opts.get_int("O3")) {
			// Trimmed existentials are a precondition to program optimizations
			o::dbg() << "Adding export outer quantifiers brancher ..." << endl << endl;
			begin.branchers.push_back(bind(&driver::brancher_export_outer_quantifiers, this, placeholders::_1));
		}
		optimized = optimize_once(rp, begin);
		step_transform(optimized, [&](raw_prog &rp) {
			plan o1(bs);
			// This transformation is a prerequisite to the CQC and binary
			// transformations, hence its more general activation condition.
			o::dbg() << "Adding dnf brancher in begin..." << endl << endl;
			o1.branchers.push_back(bind(&driver::brancher_to_dnf, this, placeholders::_1));
			if (!opts.get_int("O3")) {
				o::dbg() << "Adding split heads brancher in begin..." << endl << endl;
				o1.branchers.push_back(bind(&driver::brancher_split_heads, this, placeholders::_1));
			}
			// Though this is a binary transformation, rules will become
			// ternary after timing guards are added
			optimized = optimize_once(rp, o1);
			if(opts.enabled("O2")) {
				plan o2_loop(bs), o2_once(bs);
				o::dbg() << "Adding Minimizer brancher ..." << endl << endl;
				o2_once.branchers.push_back(bind(&driver::brancher_minimize, this, placeholders::_1));
				optimized = optimize_loop(optimized, o2_once);
				o::dbg() << "Adding Z3 brancher ..." << endl << endl;
				o2_loop.branchers.push_back(bind(&driver::brancher_subsume_queries, this, placeholders::_1));
				o::dbg() << "Adding rulse factor brancher ..." << endl << endl;
				o2_loop.branchers.push_back(bind(&driver::brancher_factor_rules, this, placeholders::_1));
				optimized = optimize_loop(optimized, o2_loop);
			}
			plan end(bs);
			o::dbg() << "Adding split bodies brancher in loop..." << endl << endl;
			end.branchers.push_back(bind(&driver::brancher_split_bodies, this, placeholders::_1));
			o::dbg() << "Step Transformed Program:" << endl << rp << endl;
			end.branchers.push_back(bind(&driver::brancher_eliminate_dead_variables, this, placeholders::_1));
			rp = optimize_once(optimized, end);
			o::dbg() << "Current:" << endl << rp << endl;
		});
	}
}

void optimize(changed_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<change>>  optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current change and try to optimize again if needed
	for (auto it = optimizations.begin(); it != optimizations.end(); ++it) {
		(*it).get()->operator()(mutated);
	}
}

void optimize_loop(changed_prog& mutated, bounder& bounder, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<change>>  optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current change and try to optimize again if needed
	powerset_range<std::shared_ptr<change>> subsets(optimizations);
	for (auto it = ++subsets.begin(); it != subsets.end(); ++it) {
		changed_prog new_mutated(mutated);
		vector<std::shared_ptr<change>> v = *it;
		for (auto mt = v.begin(); mt != v.end(); ++mt) (*mt).get()->operator()(new_mutated);
		if (bounder.bound(new_mutated)) {
			optimize_loop(new_mutated, bounder, branchers);
		}
	}
}

/*!
 * Optimize a raw program
 */
flat_prog optimize_once(flat_prog &program, plan &plan) {
	// the first mutated program just contain the original program as additions.
	changed_prog mutated {program};
	o::dbg() << "Applying optimizations ..." << endl << endl;
	optimize(mutated, plan.branchers); 
	plan.bndr.get().bound(mutated);
	return plan.bndr.get().solution();
}

flat_prog optimize_loop(flat_prog &program, plan &plan) {
	// loop over the branchers.
	changed_prog mutated {program};
	o::dbg() << "Looping over optimizations ..." << endl << endl;
	optimize_loop(mutated, plan.bndr, plan.branchers);
	return plan.bndr.get().solution();
}

#endif // CHANGE_ME

class change_del_rule : public virtual change  {
public:
	explicit change_del_rule(flat_prog &d): change(d) { }
	explicit change_del_rule(vector<term> &r): change(r) { }

	bool operator()(changed_prog &cp) const override {
		for (auto& r: clashing)	cp.current.erase(r);
		return true;
	}
};

class change_add_rule : public virtual change  {
public:
	vector<term> add;

	explicit change_add_rule(vector<term> &a): add(a) { }
	explicit change_add_rule(vector<term> &a, flat_prog d): change(d), add(a) { }
	explicit change_add_rule(vector<term> &a, vector<term> d): change(d), add(a)  { }

	bool operator()(changed_prog &cp) const override {
		cp.current.insert(add);
		return true;
	}
};

#ifdef DELETE_ME
/* Recurse through the given formula tree in pre-order calling the given
 * function with the accumulator. */

template<typename X, typename F>
X prefold_tree2(raw_form_tree &t, X acc, const F &f) {
	const X &new_acc = f(t, acc);
	switch(t.type) {
		case elem::ALT: case elem::AND: case elem::IMPLIES: case elem::COIMPLIES:
				case elem::EXISTS: case elem::FORALL: case elem::UNIQUE:
			// Fold through binary trees by threading accumulator through both
			// the LHS and RHS
			return prefold_tree2(*t.r, prefold_tree2(*t.l, new_acc, f), f);
		// Fold though unary trees by threading accumulator through this
		// node then single child
		case elem::NOT: return prefold_tree2(*t.l, new_acc, f);
		// Otherwise for leaf nodes like terms and variables, thread
		// accumulator through just this node
		default: return new_acc;
	}
}

/* Update the number and characters counters as well as the distinct
 * symbol set to account for the given term. */

void update_element_counts2(const raw_term &rt, set<elem> &distinct_syms,
		int_t &char_count, int_t &max_int) {
	for(const elem &el : rt.e)
		if(el.type == elem::NUM) max_int = max(max_int, el.num);
		else if(el.type == elem::SYM) distinct_syms.insert(el);
		else if(el.type == elem::CHR) char_count = 256;
} 

/* Compute the number of bits required to represent first the largest
 * integer in the given program and second the universe. */

pair<int_t, int_t> prog_bit_len2(const raw_prog &rp) {
	int_t max_int = 0, char_count = 0;
	set<elem> distinct_syms;

	for(const raw_rule &rr : rp.r) {
		// Updates the counters based on the heads of the current rule
		for(const raw_term &rt : rr.h)
			update_element_counts2(rt, distinct_syms, char_count, max_int);
		// If this is a rule, update the counters based on the body
		if(rr.is_dnf() || rr.is_form()) {
			raw_form_tree prft = *rr.get_prft();
			prefold_tree2(prft, monostate {},
				[&](const raw_form_tree &t, monostate) -> monostate {
					if(t.type == elem::NONE)
						update_element_counts2(*t.rt, distinct_syms, char_count, max_int);
					return monostate {};
				});
		}
	}
	// Now compute the bit-length of the largest integer found
	size_t int_bit_len = 0, universe_bit_len = 0,
		max_elt = max_int + char_count + distinct_syms.size();
	for(; max_int; max_int >>= 1, int_bit_len++);
	for(; max_elt; max_elt >>= 1, universe_bit_len++);
	o::dbg() << "Integer Bit Length: " << int_bit_len << endl;
	o::dbg() << "Universe Bit Length: " << universe_bit_len << endl << endl;
	return {int_bit_len, universe_bit_len};
} 

/*! Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. */

std::vector<std::shared_ptr<change>> driver::brancher_subsume_queries(changed_prog &mp) {
	//TODO Check if z3 context should be static?
	const auto &[int_bit_len, universe_bit_len] = prog_bit_len2(mp.current);
	z3_context ctx(int_bit_len, universe_bit_len);

	std::vector<std::shared_ptr<change>> mutations;
	vector<raw_rule> reduced;
	for (raw_rule &rr : mp.current.r) {
		bool subsumed = false;
		for (auto nrr = reduced.begin(); nrr != reduced.end();) {
			if (check_qc(rr, *nrr, ctx)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				mutation_del_rule del(rr);
				mutations.push_back(std::make_shared<mutation_del_rule>(del));
				subsumed = true;
				break;
			} else if (check_qc(*nrr, rr, ctx)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				reduced.erase(nrr);
				mutation_del_rule del(*nrr);
				mutations.push_back(std::make_shared<mutation_del_rule>(del));

			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if (!subsumed) reduced.push_back(rr);
	}
	return mutations;
} 

struct mutation_minimize : public virtual change  {
	driver &drvr;

	mutation_minimize(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		const auto &[int_bit_len, universe_bit_len] = prog_bit_len2(mp.current);
		z3_context ctx(int_bit_len, universe_bit_len);
		o::dbg() << "Minimizing rules ..." << endl << endl;
//		auto f = [this, &z3_ctx](const raw_rule &rr1, const raw_rule &rr2)
//			{ return drvr.check_qc(rr1, rr2, z3_ctx); };
		for(auto rr: mp.current.r) {
			drvr.minimize(rr, ctx);
		}
		o::dbg() << "Minimized:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_minimize(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_minimize m(*this);
	mutations.push_back(std::make_shared<mutation_minimize>(m));
	return mutations; 
} 

struct mutation_factor_rules : public virtual change  {
	driver &drvr;

	mutation_factor_rules(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Factoring rules..." << endl << endl;
		drvr.factor_rules(mp.current);
		o::dbg() << "Factored Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_factor_rules(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_factor_rules m(*this);
	mutations.push_back(std::make_shared<mutation_factor_rules>(m));
	return mutations; 
}

struct mutation_to_split_heads : public virtual change  {
	driver &drvr;

	mutation_to_split_heads(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Splitting heads ..." << endl;
		drvr.split_heads(mp.current);
		o::dbg() << "Binary Program:" << endl << mp.current << endl;
		return false;
	}
};

vector<std::shared_ptr<change>> driver::brancher_split_heads(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_to_split_heads m(*this);
	mutations.push_back(std::make_shared<mutation_to_split_heads>(m));
	return mutations;
}

struct mutation_eliminate_dead_variables : public virtual change  {
	driver &drvr;

	mutation_eliminate_dead_variables(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Eliminating dead variables ..." << endl << endl;
		drvr.eliminate_dead_variables(mp.current);
		o::dbg() << "Stripped TML Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_eliminate_dead_variables(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_eliminate_dead_variables m(*this);
	mutations.push_back(std::make_shared<mutation_eliminate_dead_variables>(m));
	return mutations;
}

struct mutation_split_bodies : public virtual change  {
	driver &drvr;

	mutation_split_bodies(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Splitting bodies ..." << endl;
		drvr.transform_bin(mp.current);
		o::dbg() << "Binary Program:" << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_split_bodies(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_split_bodies m(*this);
	mutations.push_back(std::make_shared<mutation_split_bodies>(m));
	return mutations;
}

#endif // DELETE_ME