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
#include <memory>
#include <fstream>
#include <numeric>
#include <optional>
#include <ranges>

#include "driver.h"
#include "err.h"
#include "builtins.h"
#include "cpp_gen.h"

using namespace std;

#ifdef __EMSCRIPTEN__
#include "../js/embindings.inc.h"
#endif

namespace idni {

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const pair<ccs, size_t>& p);

void driver::transform_len(raw_term& r, const strs_t& s) {
	for (size_t n = 1; n < r.e.size(); ++n)
		if (	r.e[n].type == elem::SYM && r.e[n].e == "len" &&
			n+3 < r.e.size() &&
			r.e[n+1].type == elem::OPENP &&
			r.e[n+2].type == elem::SYM &&
			r.e[n+3].type == elem::CLOSEP) {
			auto it = s.find(r.e[n+2].e);
			int_t len = it == s.end() ? 0 : it->second.size();
			r.e.erase(r.e.begin()+n,r.e.begin()+n+4),
			r.e.insert(r.e.begin()+n, elem(len)),
			r.calc_arity(current_input);
		}
}

string_t driver::directive_load(const directive& d) {
	if (d.type == directive::CMDLINEFILE) {
		int_t a = d.n - 1;
		if (a >= 0 && a < opts.pargc())
			return to_string_t(input::file_read(opts.pargv(a)));
		else parse_error(err_num_cmdline);
		return {};
	}
	string_t str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	switch (d.type) {
		case directive::FNAME:
			return to_string_t(input::file_read(to_string(str)));
		case directive::STDIN: return std::move(pd.std_input);
		default: return unquote(str);
	}
	DBGFAIL;
}

signature get_signature(const raw_term &rt) {
	return {rt.e[0].e, rt.arity};
}

void driver::directives_load(raw_prog& p) {
	lexeme trel = null_lexeme;
	// The list of directives that have been processed so far
	int_t a;
	vector<directive> processed;
	// Iterate through the directives that remain in the program
	while (!p.d.empty()) {
		const directive d = p.d[0];
		p.d.erase(p.d.begin());
		// If this directive has been processed before, then do not repeat
		// processing
		if(find(processed.begin(), processed.end(), d) != processed.end()) continue;
		else processed.push_back(d);
		switch (d.type) {
		case directive::BWD: pd.bwd = true; break;
		case directive::TRACE: trel = d.rel.e; break;
		case directive::EDOMAIN: transform_domains(p, d); break;
		case directive::QUOTE: transform_quotes(p, d); break;
		case directive::CODEC: transform_codecs(p, d); break;
		case directive::INTERNAL:
			p.hidden_rels.insert(get_signature(d.internal_term)); break;
		case directive::CMDLINE:
			a = d.n - 1;
			if (a >= 0 && a < opts.pargc()) pd.strs
				.emplace(d.rel.e, to_string_t(opts.pargv(a)));
			else parse_error(err_num_cmdline);
			break;
		default: pd.strs.emplace(d.rel.e, directive_load(d));
		}
	}
	p.d.insert(p.d.end(), processed.begin(), processed.end());
}

/* Reduce the top-level logical operator to a more primitive one if this
 * is possible. That is, reduce implications and co-implications to
 * conjunctions/disjunctions, and reduce uniqueness quantifications to
 * universal and existential quantifications. Useful for avoiding having
 * to separately process these operators. */

raw_form_tree expand_formula_node(const raw_form_tree &t, dict_t &d) {
	switch(t.type) {
		case elem::IMPLIES: {
			// Implication is logically equivalent to the following
			return raw_form_tree(elem::ALT,
				make_shared<raw_form_tree>(elem::NOT, t.l), t.r);
		} case elem::COIMPLIES: {
			// Co-implication is logically equivalent to the following
			return raw_form_tree(elem::AND,
				make_shared<raw_form_tree>(elem::IMPLIES, t.l, t.r),
				make_shared<raw_form_tree>(elem::IMPLIES, t.r, t.l));
		} case elem::UNIQUE: {
			// The uniqueness quantifier is logically equivalent to the
			// following
			const elem evar = elem::fresh_var(d), qvar = *(t.l->el);
			map<elem, elem> renames {{qvar, evar}};
			raw_form_tree t_copy = *t.r;
			rename_variables(t_copy, renames, gen_id_var);
			return raw_form_tree(elem::EXISTS,
				make_shared<raw_form_tree>(qvar),
				make_shared<raw_form_tree>(elem::AND, t.r,
					make_shared<raw_form_tree>(elem::FORALL,
						make_shared<raw_form_tree>(evar),
						make_shared<raw_form_tree>(elem::IMPLIES,
							make_shared<raw_form_tree>(t_copy),
							make_shared<raw_form_tree>(
								raw_term(raw_term::EQ, { evar, elem(elem::EQ), qvar }))))));
		} default: {
			return t;
		}
	}
}

/* Check if the given variable is limited in its scope with respect to
 * the given variable. If the element is not a variable, then it is
 * automatically limited. */

bool driver::is_limited(const elem &var, set<elem> &wrt,
		map<elem, const raw_form_tree*> &scopes) {
	if(var.type == elem::VAR) {
		return is_limited(var, *scopes[var], wrt, scopes);
	} else {
		return true;
	}
}

/* Algorithm to check rule safety based on "Safe Database Queries with
 * Arithmetic Relations" by Rodney Topor. */

bool driver::is_limited(const elem &var, const raw_form_tree &t,
		set<elem> &wrt, map<elem, const raw_form_tree*> &scopes) {

	switch(t.type) {
		case elem::IMPLIES:
			// Process the expanded formula instead
			return is_limited(var, expand_formula_node(t, dict), wrt, scopes);
		case elem::COIMPLIES:
			// Process the expanded formula instead
			return is_limited(var, expand_formula_node(t, dict), wrt, scopes);
		case elem::AND: {
			// var is limited in a && b if var is limited in a or b
			vector<const raw_form_tree*> ands;
			// Collect all the conjuncts within the tree top
			t.flatten_associative(elem::AND, ands);
			for(const raw_form_tree* &tree : ands) {
				if(is_limited(var, *tree, wrt, scopes))
					return true;
			}
			return false;
		} case elem::ALT: {
			// var is limited in a || b if var is limited in both a and b
			vector<const raw_form_tree*> alts;
			// Collect all the disjuncts within the tree top
			t.flatten_associative(elem::ALT, alts);
			for(const raw_form_tree* &tree : alts) {
				if(!is_limited(var, *tree, wrt, scopes)) {
					return false;
				}
			}
			return true;
		} case elem::NOT: {
			switch(t.l->type) {
				case elem::NOT: {
					// var is limited in ~~a if var is limited in a
					return is_limited(var, *t.l->l, wrt, scopes);
				} case elem::AND: {
					// var is limited in ~(a && b) if var is limited in both ~a and ~b
					vector<const raw_form_tree*> ands;
					// Collect all the conjuncts within the tree top
					t.l->flatten_associative(elem::AND, ands);
					for(const raw_form_tree* &tree : ands) {
						if(!is_limited(var, raw_form_tree(elem::NOT, make_shared<raw_form_tree>(*tree)), wrt, scopes)) {
							return false;
						}
					}
					return true;
				} case elem::ALT: {
					// var is limited in ~(a || b) if var is limited in both ~a or ~b
					vector<const raw_form_tree*> alts;
					// Collect all the disjuncts within the tree top
					t.l->flatten_associative(elem::ALT, alts);
					for(const raw_form_tree* &tree : alts) {
						if(is_limited(var, raw_form_tree(elem::NOT, make_shared<raw_form_tree>(*tree)), wrt, scopes)) {
							return true;
						}
					}
					return false;
				} case elem::IMPLIES: {
					// Process the expanded formula instead
					return is_limited(var, raw_form_tree(elem::NOT,
						make_shared<raw_form_tree>(expand_formula_node(*t.l, dict))), wrt, scopes);
				} case elem::COIMPLIES: {
					// Process the expanded formula instead
					return is_limited(var, raw_form_tree(elem::NOT,
						make_shared<raw_form_tree>(expand_formula_node(*t.l, dict))), wrt, scopes);
				} case elem::EXISTS: case elem::FORALL: {
					const elem &qvar = *t.l->l->el;
					if(qvar == var) {
						// In this case, the quantifier's variable shadows the variable,
						// var, whose limitation we are checking. So var cannot be
						// limited with respect to this formula.
						return false;
					} else {
						// var is limited in ~exists ?y G if var is limited in ~G
						// Same for forall
						map<elem, const raw_form_tree*> new_scopes = scopes;
						new_scopes[qvar] = &*t.l->r;
						return is_limited(var,
							raw_form_tree(elem::NOT, t.l->r), wrt, new_scopes);
					}
				} case elem::UNIQUE: {
					// Process the expanded formula instead
					return is_limited(var, raw_form_tree(elem::NOT,
						make_shared<raw_form_tree>(expand_formula_node(*t.l, dict))), wrt, scopes);
				} case elem::NONE: {
					const raw_term &rt = *t.l->rt;
					switch(rt.extype) {
						case raw_term::ARITH: case raw_term::LEQ: {
							// If variable is used in atomic or arithmetic formula, then
							// it is limited because it is a number and all numbers are
							// less than 2^n
							for(size_t i = 0; i < rt.e.size(); i++) {
								if(rt.e[i] == var) return true;
							}
							return false;
						} default: {
							return false;
						}
					}
				} default: {
					return false;
				}
			}
		} case elem::EXISTS: case elem::FORALL: {
			const elem &qvar = *t.l->el;
			if(qvar == var) {
				// In this case, the quantifier's variable shadows the variable,
				// var, whose limitation we are checking. So var cannot be
				// limited with respect to this formula.
				return false;
			} else {
				// var is limited in exists ?y G if var is limited in G
				// Same for forall
				map<elem, const raw_form_tree*> new_scopes = scopes;
				new_scopes[qvar] = &*t.r;
				return is_limited(var, *t.r, wrt, new_scopes);
			}
		} case elem::UNIQUE: {
			// Process the expanded formula instead
			return is_limited(var, expand_formula_node(t, dict), wrt, scopes);
		} case elem::NONE: {
			const raw_term &rt = *t.rt;
			switch(rt.extype) {
				case raw_term::REL: case raw_term::ARITH: case raw_term::LEQ: case raw_term::BLTIN: {
					// If variable is used in atomic or arithmetic formula, then
					// it is limited because it is a number and all numbers are
					// less than 2^n
					for(size_t i = 0; i < rt.e.size(); i++) {
						if(rt.e[i] == var) return true;
					}
					return false;
				} case raw_term::EQ: {
					const elem &other = rt.e[0] == var ? rt.e[2] : rt.e[0];
					if(rt.e[0] != var && rt.e[2] != var) {
						return false;
					} else if(wrt.find(var) == wrt.end()) {
						// Handle the finiteness dependencies {1} -> 0 and {0} -> 1
						wrt.insert(var);
						bool res = is_limited(other, wrt, scopes);
						wrt.erase(var);
						return res;
					} else {
						return false;
					}
				} default: {
					return false;
				}
			}
		} default:
			assert(false); //should never reach here
			return false;
	}
}

/* Check whether for every subformula exists ?y G, the variable ?y is
 * limited in G. Also check whether for every subformula forall ?y G,
 * the variable ?y is limited in ~G. If not, return the offending
 * variable. */

optional<elem> driver::all_quantifiers_limited(const raw_form_tree &t,
		map<elem, const raw_form_tree*> &scopes) {

	switch(t.type) {
		case elem::IMPLIES:
			// Process the expanded formula instead
			return all_quantifiers_limited(expand_formula_node(t, dict), scopes);
		case elem::COIMPLIES:
			// Process the expanded formula instead
			return all_quantifiers_limited(expand_formula_node(t, dict), scopes);
		case elem::AND: {
			// Collect all the conjuncts within the tree top
			vector<const raw_form_tree*> ands;
			t.flatten_associative(elem::AND, ands);
			for(const raw_form_tree* &tree : ands) {
				if(auto unlimited_var = all_quantifiers_limited(*tree, scopes)) {
					return unlimited_var;
				}
			}
			return nullopt;
		} case elem::ALT: {
			// Collect all the disjuncts within the tree top
			vector<const raw_form_tree*> alts;
			t.flatten_associative(elem::ALT, alts);
			for(const raw_form_tree* &tree : alts) {
				if(auto unlimited_var = all_quantifiers_limited(*tree, scopes)) {
					return unlimited_var;
				}
			}
			return nullopt;
		} case elem::NOT: {
			return all_quantifiers_limited(*t.l, scopes);
		} case elem::EXISTS: {
			set<elem> wrt;
			const elem &var = *t.l->el;
			map<elem, const raw_form_tree*> new_scopes = scopes;
			new_scopes[var] = &*t.r;
			if(is_limited(var, *t.r, wrt, new_scopes)) {
				return all_quantifiers_limited(*t.r, new_scopes);
			} else {
				return var;
			}
		} case elem::FORALL: {
			set<elem> wrt;
			const elem &var = *t.l->el;
			map<elem, const raw_form_tree*> new_scopes = scopes;
			new_scopes[var] = &*t.r;
			if(is_limited(var, raw_form_tree(elem::NOT, t.r), wrt, new_scopes)) {
				return all_quantifiers_limited(*t.r, new_scopes);
			} else {
				return var;
			}
		} case elem::UNIQUE: {
			// Process the expanded formula instead
			return all_quantifiers_limited(expand_formula_node(t, dict), scopes);
		} case elem::NONE: {
			return nullopt;
		} default:
			assert(false); //should never reach here
			return false;
	}
}

/* Check whether the given formula tree is safe and return the offending
 * variable if not. This means that every free variable in the tree is
 * limited and that all its quantifiers are limited. */

optional<elem> driver::is_safe(const raw_form_tree &t) {
	set<elem> free_vars = collect_free_vars(t);
	map<elem, const raw_form_tree*> scopes;
	for(const elem &free_var : free_vars) {
		scopes[free_var] = &t;
	}
	for(const elem &free_var : free_vars) {
		set<elem> wrt;
		if(!is_limited(free_var, t, wrt, scopes)) {
			return free_var;
		}
	}
	return all_quantifiers_limited(t, scopes);
}

/* Check whether the given rule is safe and return the offending variable if
 * not. This means that every non-goal head's variables are limited in the body
 * and that the body itself is safe. Only single heads are allowed to simplify
 * handling of deletions. */

optional<elem> driver::is_safe(const raw_rule &rr) {
	set<elem> free_vars;
	if(rr.type != raw_rule::GOAL) {
		vector<elem> bound_vars;
		// Only collect the free variables of positive heads because we
		// can always guard the body of a rule with a negative head with
		// the negation of the head to obtain an equivalent rule.
		collect_free_vars(rr.h[0], bound_vars, free_vars);
	}
	if(optional<raw_form_tree> prft = rr.get_prft()) {
		// If the head is negative, then treat the head negated as an implicit body
		// term as it only makes sence to delete a fact that is already present.
		if(rr.h[0].neg) {
			prft = raw_form_tree(elem::AND,
				make_shared<raw_form_tree>(rr.h[0].negate()),
				make_shared<raw_form_tree>(*prft));
		}
		// Initialize variable scopes, this is needed for the safety checking
		// algorithm to verify limitations by going through equality terms.
		vector<elem> bound_vars;
		collect_free_vars(*prft, bound_vars, free_vars);
		// All the formulas free variables have "global" formula scope
		map<elem, const raw_form_tree*> scopes;
		for(const elem &free_var : free_vars) {
			scopes[free_var] = &*prft;
		}

		// Ensure that all the head variables and other free variables are
		// limited in the formula
		for(const elem &var : free_vars) {
			set<elem> wrt;
			if(!is_limited(var, *prft, wrt, scopes)) {
				return var;
			}
		}
		// Lastly check that all the quantification subformula variables are
		// limited in their bodies
		return all_quantifiers_limited(*prft, scopes);
	} else {
		// If there free variables in the head but no body, then all of them are not
		// limited. Any one of them can be a witness
		return free_vars.empty() ? nullopt : make_optional(*free_vars.begin());
	}
}

/* Check whether a given TML program is safe and return the offending
 * variable and rule if not. This means that every rule must be safe. */

optional<pair<elem, raw_rule>> driver::is_safe(raw_prog &rp) {
	// Ignore the outermost existential quantifiers
	export_outer_quantifiers(rp);

	for(const raw_rule &rr : rp.r) {
		if(auto unlimited_var = is_safe(rr)) {
			return make_pair(*unlimited_var, rr);
		}
	}
	return nullopt;
}

/* Checks if the body of the given rule is conjunctive. */

bool is_cq(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is a proper rule
	if(!rr.is_dnf()) return false;
	// Ensure that each body term is positive and is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.neg || rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* Checks if the body of the given rule is conjunctive with negation. */

bool is_cqn(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is a proper rule
	if(!rr.is_dnf()) return false;
	// Ensure that each body term is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* Recurse through the given formula tree in pre-order calling the given
 * function with the accumulator. */

template<typename X, typename F>
		X prefold_tree(raw_form_tree &t, X acc, const F &f) {
	const X &new_acc = f(t, acc);
	switch(t.type) {
		case elem::ALT: case elem::AND: case elem::IMPLIES: case elem::COIMPLIES:
				case elem::EXISTS: case elem::FORALL: case elem::UNIQUE:
			// Fold through binary trees by threading accumulator through both
			// the LHS and RHS
			return prefold_tree(*t.r, prefold_tree(*t.l, new_acc, f), f);
		// Fold though unary trees by threading accumulator through this
		// node then single child
		case elem::NOT: return prefold_tree(*t.l, new_acc, f);
		// Otherwise for leaf nodes like terms and variables, thread
		// accumulator through just this node
		default: return new_acc;
	}
}

/* Recurse through the given formula tree in post-order calling the
 * given function with the accumulator. */

template<typename X, typename F>
		X postfold_tree(raw_form_tree &t, X acc, const F &f) {
	switch(t.type) {
		case elem::ALT: case elem::AND: case elem::IMPLIES: case elem::COIMPLIES:
				case elem::EXISTS: case elem::FORALL: case elem::UNIQUE:
			// Fold through binary trees by threading accumulator through both
			// the LHS and RHS
			return f(t, postfold_tree(*t.r, postfold_tree(*t.l, acc, f), f));
		// Fold though unary trees by threading accumulator through the
		// single child then this node
		case elem::NOT: return f(t, postfold_tree(*t.l, acc, f));
		// Otherwise for leaf nodes like terms and variables, thread
		// accumulator through just this node
		default: return f(t, acc);
	}
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
	for(auto &[var, covar] : vs) {
		if(find(nonfree_vars.begin(), nonfree_vars.end(), covar) !=
				nonfree_vars.end()) {
			orig_vars.insert(var);
		}
	}
}

/* Count the number of rules (including the given one) that derive facts
 * for the same relation that the given rule derives facts for. */

int_t driver::count_related_rules(const raw_rule &rr1, const raw_prog &rp) {
	int_t count = 0;
	for(const raw_rule &rr2 : rp.r) {
		if(rr1.h[0].e[0] == rr2.h[0].e[0] &&
				rr1.h[0].e.size() == rr2.h[0].e.size()) {
			count++;
		}
	}
	return count;
}

/* Takes two DNF rules and returns true if the first is "smaller" than the
 * second. Smaller means less conjuncts in the body, and in the case of a tie
 * means less arguments in the head. */

bool rule_smaller(const raw_rule &rr2, const raw_rule &rr1) {
	if(rr1.b.size() == 1 && rr2.b.size() == 1) {
		if(rr1.b[0].size() == rr2.b[0].size()) {
			return rr1.h[0].e.size() > rr2.h[0].e.size();
		} else {
			return rr1.b[0].size() > rr2.b[0].size();
		}
	} else {
		return rr1.b.size() > rr2.b.size();
	}
}

/* Collect the variables used in the given terms and return. */

void collect_vars(const raw_term &rt, set<elem> &vars) {
	for(const elem &e : rt.e) {
		if(e.type == elem::VAR) {
			vars.insert(e);
		}
	}
}

/* Collect the variables used in the given terms and return. */
template <class InputIterator>
void collect_vars(InputIterator first, InputIterator last, set<elem> &vars) {
	for(; first != last; first++) {
		collect_vars(*first, vars);
	}
}

/* Collect the variables used in the head and the positive terms of the
 * given rule and return. */
void collect_vars(const raw_rule &rr, set<elem> &vars) {
	collect_vars(rr.h[0], vars);
	for(const raw_term &tm : rr.b[0]) {
		collect_vars(tm, vars);
	}
}

/* Update the number and characters counters as well as the distinct
 * symbol set to account for the given term. */

void update_element_counts(const raw_term &rt, set<elem> &distinct_syms,
		int_t &char_count, int_t &max_int) {
	for(const elem &el : rt.e)
		if(el.type == elem::NUM) max_int = max(max_int, el.num);
		else if(el.type == elem::SYM) distinct_syms.insert(el);
		else if(el.type == elem::CHR) char_count = 256;
}

/* Make relations mapping list ID's to their heads and tails. Domain's
 * first argument is the relation into which it should put the domain it
 * creates, its second argument is the domain size of of its tuple
 * elements, and its third argument is the maximum tuple length. */

bool driver::transform_domains(raw_prog &rp, const directive& drt) {
	o::dbg() << "Generating domain for: " << drt << endl;
	// Ensure that we're working on a DOMAIN directive
	if(drt.type != directive::EDOMAIN) return false;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem out_rel = drt.domain_sym;
	// This transformation will automatically generate non-negative
	// numbers up to this limit for inclusion in domain
	int_t gen_limit = drt.limit_num.num;
	// The maximum arity of the desired domain is the first symbol
	// between the inner parentheses
	int_t max_arity = drt.arity_num.num;
	// The number of distinct lists of elements less than gen_limit and
	// with length less than max_limit
	int_t max_id = gen_limit == 1 ? max_arity + 1 :
		(pow(gen_limit, max_arity + 1) - 1) / (gen_limit - 1);

	// Initialize the symbols, variables, and operators used in the
	// domain creation rule
	elem lt_elem(elem::LT, dict.get_lexeme("<")),
		leq_elem(elem::LEQ, dict.get_lexeme("<=")),
		plus_elem(elem::ARITH, t_arith_op::ADD, dict.get_lexeme("+")),
		equals_elem(elem::EQ, dict.get_lexeme("=")),
		list_id = elem::fresh_var(dict), list_fst = elem::fresh_var(dict),
		list_rst = elem::fresh_var(dict), pred_id = elem::fresh_var(dict),
		divisor_x_quotient = gen_limit == 1 ? list_rst : elem::fresh_var(dict);

	// Make two relations for manipulating domains, the fst relation
	// relates a list ID to its head, and the rst relation relates a
	// list ID to its tail.
	raw_term fst_head({concat(out_rel, "_fst"), elem_openp, list_id,
		list_fst, elem_closep});
	raw_term rst_head({concat(out_rel, "_rst"), elem_openp, list_id,
		list_rst, elem_closep});

	// The body of the fst and rst rules. Since lists are encoded by
	// multiplying each element by the exponent of some base.
	// Euclidean division is required to extract list elements from a
	// given ID.
	vector<raw_term> bodie = {
		// 0 < list_id
		raw_term(raw_term::LEQ, {list_id, leq_elem, elem(0)}).negate(),
 		// list_id < max_id
		raw_term(raw_term::LEQ, {elem(max_id), leq_elem, list_id}).negate(),
		// 0 <= list_fst
		raw_term(raw_term::LEQ, {elem(0), leq_elem, list_fst}),
		// list_fst < gen_limit
		raw_term(raw_term::LEQ, {elem(gen_limit), leq_elem, list_fst}).negate(),
		// 0 <= list_rst
		raw_term(raw_term::LEQ, {elem(0), leq_elem, list_rst}),
		// list_rst < list_id
		raw_term(raw_term::LEQ, {list_id, leq_elem, list_rst}).negate(),
		// pred_id + 1 = list_id
		raw_term(raw_term::ARITH, t_arith_op::ADD, {pred_id, plus_elem,
			elem(1), equals_elem, list_id}),
		// divisor_x_quotient + list_fst = pred_id
		raw_term(raw_term::ARITH, t_arith_op::ADD, {divisor_x_quotient,
			plus_elem, list_fst, equals_elem, pred_id})
		};
	// Multiplication seems to cause the solver to hang. Since the
	// divisor is the value of gen_limit, we can express divisor *
	// quotient by repeated addition, or for smaller BDDs, by repeated
	// doubling.
	elem quotient_elem = divisor_x_quotient;
	for(int_t quotient = gen_limit; quotient > 1;) {
		// If current quotient is odd, then it will need to be expressed
		// by doubling something and adding the divisor to it
		if(quotient % 2 == 1) {
			elem new_quotient_elem = elem::fresh_var(dict);
			// new_quotient_elem + list_rst = quotient_elem
			bodie.push_back(raw_term(raw_term::ARITH, t_arith_op::ADD,
				{new_quotient_elem, plus_elem, list_rst, equals_elem, quotient_elem}));
			quotient_elem = new_quotient_elem;
			quotient --;
		}
		// If current quotient is more than or equal to 2, then it can
		// be expressed by doubling something
		if(quotient / 2 > 0) {
			elem new_quotient_elem =
				quotient / 2 == 1 ? list_rst : elem::fresh_var(dict);
			// new_quotient_elem + new_quotient_elem = quotient_elem
			bodie.push_back(raw_term(raw_term::ARITH, t_arith_op::ADD,
				{new_quotient_elem, plus_elem, new_quotient_elem, equals_elem,
					quotient_elem}));
			quotient_elem = new_quotient_elem;
			quotient /= 2;
		}
	}
	// Finally create the domain rules
	rp.r.push_back(raw_rule({fst_head, rst_head}, bodie));
	// Also make the nil list
	raw_term nil_fact({ concat(out_rel, "_nil"), elem_openp, elem(0), elem_closep });
	rp.r.push_back(raw_rule(nil_fact));
	// To prevent spurious (i.e. purely modular) solutions to the
	// modular equation defining lists, we should artificially
	// increase the modulus to a number which the arithmetic
	// operations cannot reach (due to their bounds).
	raw_term mod_fact({ concat(out_rel, "_mod"), elem_openp,
		elem(gen_limit * max_id), elem_closep });
	rp.r.push_back(raw_rule(mod_fact));

	// Lists are sometimes used to encode interpreter memory. In this
	// scenario, it is useful to treat the longest lists as possible
	// memory states
	elem current_list = elem::fresh_var(dict), next_list = elem::fresh_var(dict);
	// The relation that will contain all the longest lists
	raw_term max_head({ concat(out_rel, "_max"),
		elem_openp, current_list, elem_closep });
	// The body essentially ensures that the given list has the given
	// number of nodes. Note that node values are ignored here.
	vector<raw_term> max_body;
	for(int_t i = 0; i < max_arity; i++) {
		max_body.push_back(raw_term({ concat(out_rel, "_rst"),
			elem_openp, current_list, next_list, elem_closep }));
		current_list = next_list;
		next_list = elem::fresh_var(dict);
	}
	// Not strictly necessary. Makes sure that the list end occurs
	// after the arity_max nodes.
	max_body.push_back(raw_term({ concat(out_rel, "_nil"),
		elem_openp, current_list, elem_closep }));
	// Create the longest list rule.
	rp.r.push_back(raw_rule(max_head, max_body));
	// Make the list relations hidden
	rp.hidden_rels.insert(get_signature(fst_head));
	rp.hidden_rels.insert(get_signature(rst_head));
	rp.hidden_rels.insert(get_signature(max_head));
	rp.hidden_rels.insert(get_signature(nil_fact));
	rp.hidden_rels.insert(get_signature(mod_fact));
	// Successfully executed directive
	o::dbg() << "Generated domain for: " << drt << endl;
	return true;
}

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one. */

elem driver::quote_elem(const elem &e, map<elem, elem> &variables,
		dict_t &d) {
	if(variables.find(e) != variables.end()) {
		return variables[e];
	} else {
		// Since the current variable lacks a designated substitute,
		// make one and record the mapping.
		return variables[e] = (e.type == elem::VAR ? elem::fresh_sym(d) : e);
	}
}

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one such that it uses the lowest 0-based index. */

elem driver::numeric_quote_elem(const elem &e,
		map<elem, elem> &variables) {
	if(variables.find(e) != variables.end()) {
		return variables[e];
	} else {
		// Since the current variable lacks a designated substitute,
		// make one and record the mapping.
		return variables[e] = (e.type == elem::VAR ? elem(int_t(variables.size())) : e);
	}
}

/* Iterate through terms and associate each unique variable with unique
 * fresh symbol. */

raw_rule driver::freeze_rule(raw_rule rr,
		map<elem, elem> &freeze_map, dict_t &d) {
	for(raw_term &tm : rr.h) {
		if(tm.extype == raw_term::REL) {
			for(size_t i = 2; i < tm.e.size() - 1; i++) {
				tm.e[i] = quote_elem(tm.e[i], freeze_map, d);
			}
		}
	}
	for(vector<raw_term> &bodie : rr.b) {
		for(raw_term &tm : bodie) {
			if(tm.extype == raw_term::REL) {
				for(size_t i = 2; i < tm.e.size() - 1; i++) {
					tm.e[i] = quote_elem(tm.e[i], freeze_map, d);
				}
			}
		}
	}
	return rr;
}

/* Takes a raw term and returns its quotation within a relation of the
 * given name. The names of variable elements within the raw term are
 * added to the variables map. */

elem driver::quote_term(const raw_term &head, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, map<elem, elem> &variables,
		int_t &part_count) {
	elem term_id(part_count++);
	if(head.extype == raw_term::REL) {
		elem elems_id = elem::fresh_var(dict), tags_id = elem::fresh_var(dict),
			elems_hid = elems_id, tags_hid = tags_id;
		vector<raw_term> params_body, param_types_body;
		for(size_t param_idx = 2; param_idx < head.e.size() - 1; param_idx ++) {
			elem next_elems_id = elem::fresh_var(dict),
				next_tags_id = elem::fresh_var(dict);
			params_body.push_back(raw_term({concat(domain_name, "_fst"), elem_openp,
				elems_id, numeric_quote_elem(head.e[param_idx], variables),
				elem_closep}));
			params_body.push_back(raw_term({concat(domain_name, "_rst"), elem_openp,
				elems_id, next_elems_id, elem_closep}));
			param_types_body.push_back(raw_term({concat(domain_name, "_fst"), elem_openp,
				tags_id, elem(int_t(head.e[param_idx].type == elem::VAR)), elem_closep}));
			param_types_body.push_back(raw_term({concat(domain_name, "_rst"), elem_openp,
				tags_id, next_tags_id, elem_closep}));
			elems_id = next_elems_id;
			tags_id = next_tags_id;
		}
		params_body.push_back(raw_term({concat(domain_name, "_nil"), elem_openp,
			elems_id, elem_closep}));
		param_types_body.push_back(raw_term({concat(domain_name, "_nil"), elem_openp,
			tags_id, elem_closep}));
		// Add metadata to quoted term: term signature, term id, term name
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
			term_id, elem(QTERM), elem_closep })));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_term_relation"),
			elem_openp, term_id, head.e[0], elem_closep })));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_term_params"),
			elem_openp, term_id, elems_hid, elem_closep }), params_body));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_term_param_types"),
			elem_openp, term_id, tags_hid, elem_closep }), param_types_body));
	} else if(head.extype == raw_term::EQ) {
		// Add metadata to quoted term: term signature, term id, term name
		vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QEQUALS),
			term_id, numeric_quote_elem(head.e[0], variables),
			numeric_quote_elem(head.e[2], variables),
			int_t(head.e[0].type == elem::VAR), int_t(head.e[2].type == elem::VAR),
			elem_closep };
		rp.r.push_back(raw_rule(raw_term(quoted_term_e)));
	}
	if(head.neg) {
		// If this term is actually negated, then we'll make a parent for
		// this node and return its id
		elem neg_id(part_count++);
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
			neg_id, elem(QNOT), elem_closep})));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_not_body"), elem_openp,
			neg_id, term_id, elem_closep})));
		return neg_id;
	} else {
		return term_id;
	}
}

/* Recursively quotes the given formula. Say that the output relation
 * name is q, quote_formula will populate it according to the following
 * schema:
 * <quote>_type(<node ID> <node type>).
 *
 * For <node type> = RULE
 * 	<quote>_rule_head(<node ID> <head ID>).
 * 	<quote>_rule_body(<node ID> <body ID>).
 * For <node type> = TERM
 * 	<quote>_term_relation(<node ID> <term relation>).
 * 	<quote>_term_params(<node ID> <term parameter list>).
 * 	<quote>_term_param_types(<node ID> <term param type list>).
 * For <node type> = AND
 * 	<quote>_and_left(<node ID> <left node ID>).
 * 	<quote>_and_right(<node ID> <right node ID>).
 * For <node type> = ALT
 * 	<quote>_alt_left(<node ID> <left node ID>).
 * 	<quote>_alt_right(<node ID> <right node ID>).
 * For <node type> = NOT
 * 	<quote>_not_body(<node ID> <body node ID>).
 * For <node type> = FORALL
 * 	<quote>_forall_var(<node ID> <variable ID>).
 * 	<quote>_forall_body(<node ID> <body node ID>).
 * For <node type> = EXISTS
 * 	<quote>_exists_var(<node ID> <variable ID>).
 * 	<quote>_exists_body(<node ID> <body node ID>).
 * For <node type> = FACT
 *  <quote>_fact_term(<node ID> <term ID>).
 */

elem driver::quote_formula(const raw_form_tree &t, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, map<elem, elem> &variables,
		int_t &part_count) {
	const elem part_id = elem(part_count++);
	switch(t.type) {
		case elem::IMPLIES:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QIMPLIES), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_implies_left"),
				elem_openp, part_id,
				quote_formula(*t.l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_implies_right"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::COIMPLIES:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QCOIMPLIES), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_coimplies_left"),
				elem_openp, part_id,
				quote_formula(*t.l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_coimplies_right"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::AND:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QAND), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_and_left"),
				elem_openp, part_id,
				quote_formula(*t.l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_and_right"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::ALT:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QALT), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_alt_left"),
				elem_openp, part_id,
				quote_formula(*t.l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_alt_right"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::NOT:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QNOT), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_not_body"),
				elem_openp, part_id,
				quote_formula(*t.l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::EXISTS: {
			elem qvar = quote_elem(*(t.l->el), variables, dict);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QEXISTS), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_exists_var"),
				elem_openp, part_id, qvar, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_exists_body"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		} case elem::UNIQUE: {
			elem qvar = quote_elem(*(t.l->el), variables, dict);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QUNIQUE), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_unique_var"),
				elem_openp, part_id, qvar, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_unique_body"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		} case elem::NONE: {
			return quote_term(*t.rt, rel_name, domain_name, rp, variables, part_count);
			break;
		} case elem::FORALL: {
			elem qvar = quote_elem(*(t.l->el), variables, dict);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QFORALL), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_forall_var"),
				elem_openp, part_id, qvar, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_forall_body"),
				elem_openp, part_id,
				quote_formula(*t.r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		} default:
			assert(false); //should never reach here
	}
	return part_id;
}

/* Returns a symbol formed by concatenating the given string to the
 * given symbol. Used for refering to sub relations. */

elem driver::concat(const elem &rel, string suffix) {
	// Get dictionary for generating fresh symbols
	dict_t &d = dict;

	// Make lexeme from concatenating rel's lexeme with the given suffix
	return elem(elem::SYM,
		d.get_lexeme(lexeme2str(rel.e) + to_string_t(suffix)));
}

/* Returns a lexeme formed by concatenating the given string to the
 * given lexeme. Used for refering to sub relations. */

lexeme driver::concat(const lexeme &rel, string suffix) {
	// Make lexeme from concatenating rel's lexeme with the given suffix
	return dict.get_lexeme(lexeme2str(rel) + to_string_t(suffix));
}

/* Quote the given rule and put its quotation into the given raw_prog
 * under a relation given by rel_name. */

vector<elem> driver::quote_rule(const raw_rule &rr,
		const elem &rel_name, const elem &domain_name, raw_prog &rp,
		int_t &part_count) {
	// Maintain a list of the variable substitutions:
	map<elem, elem> variables;
	vector<elem> rule_ids;

	// Facts and rules have different representations in quotations. This
	// is because they are interpreted differently: facts are placed in
	// the 0th database whilst rules are fired on each iteration.
	if(rr.is_fact()) {
		for(size_t gidx = 0; gidx < rr.h.size(); gidx++) {
			const elem term_id = quote_term(rr.h[gidx], rel_name, domain_name, rp,
				variables, part_count);
			const elem rule_id = elem(part_count++);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
				rule_id, elem(QFACT), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_fact_term"), elem_openp,
				rule_id, term_id, elem_closep })));
			rule_ids.push_back(rule_id);
		}
	} else if(rr.is_dnf() || rr.is_form()) {
		const elem body_id = quote_formula(*rr.get_prft(), rel_name, domain_name,
			rp, variables, part_count);
		for(size_t gidx = 0; gidx < rr.h.size(); gidx++) {
			const elem head_id = quote_term(rr.h[gidx], rel_name, domain_name, rp,
				variables, part_count);
			const elem rule_id = elem(part_count++);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
				rule_id, elem(QRULE), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_rule_head"), elem_openp,
				rule_id, head_id, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_rule_body"), elem_openp,
				rule_id, body_id, elem_closep })));
			rule_ids.push_back(rule_id);
		}
	}
	return rule_ids;
}

/* Put the quotation of the given program into a relation of the given
 * name in the given program. */

void driver::quote_prog(const raw_prog nrp, const elem &rel_name,
		const elem &domain_name, raw_prog &rp) {
	int_t part_count = 0;
	for(size_t ridx = 0; ridx < nrp.r.size(); ridx++)
		quote_rule(nrp.r[ridx], rel_name, domain_name, rp, part_count);
}

/* Parse an STR elem into a raw_prog. */

raw_prog driver::read_prog(elem prog) {
	lexeme prog_str = {prog.e[0]+1, prog.e[1]-1};
	input *prog_in = dynii.add_string(lexeme2str(prog_str));
	prog_in->prog_lex();
	raw_prog nrp(dict);
	nrp.parse(prog_in);
	return nrp;
}

/* Make a relation representing the code given in the quotation. Quote's
 * first argument is the relation into which it should put the quotation
 * it creates, and it's second argument is the program to quote. */

bool driver::transform_quotes(raw_prog &rp, const directive &drt) {
	if(drt.type != directive::QUOTE) return false;
	o::dbg() << "Generating quotation for: " << drt << endl;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem out_rel = drt.quote_sym;
	// The relation containing the quotation arity is the second symbol
	// between the parentheses
	elem domain_sym = drt.domain_sym;
	// The formal symbol representing the quotation relation is the
	// third symbol between the parentheses
	elem quote_str = drt.quote_str;

	if(quote_str.type == elem::STR && quote_str.e[1] > quote_str.e[0] &&
			*quote_str.e[0] == '`') {
		raw_prog nrp = read_prog(quote_str);
		// Create the quotation relation
		quote_prog(nrp, out_rel, domain_sym, rp);
	}
	// Indicate success
	o::dbg() << "Generated quotation for: " << drt << endl;
	return true;
}

/* An Imhof-style interpreter can be inconvenient to debug because
 * its output tuples are encoded into numbers using modular arithmetic.
 * This transformation creates codecs for interpreters so that it's
 * easier to inspect and manipulate them.
 *
 * Codec takes four arguments: the name of the relation that will
 * contain the encodings/decodings of interpreter outputs, the formal
 * name of a relation containing the domain of the interpreter, the
 * formal name of the relation containing the interpreter, and the
 * maximum arity of the domain. */

bool driver::transform_codecs(raw_prog &rp, const directive &drt) {
	if(drt.type != directive::CODEC) return false;
	o::dbg() << "Generating codec for: " << drt << endl;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem codec_rel = drt.codec_sym;
	// The relation containing the quotation arity is the second symbol
	// between the parentheses
	elem domain_sym = drt.domain_sym;
	// The formal symbol representing the output relation is the
	// third symbol between the parentheses
	elem out_sym = drt.eval_sym;
	// The number representing the maximum arity of relations in the
	// quotation is the fourth symbol between the parentheses
	int_t max_arity = drt.arity_num.num;

	// Create the symbols and variables that will feature heavily in
	// the terms to be created below
	elem decode_tmp_rel = concat(codec_rel, "__decode"),
		name_var = elem::fresh_var(dict), timestep_var = elem::fresh_var(dict),
		next_timestep_var = elem::fresh_var(dict), params_var = elem::fresh_var(dict);

	// Create the terms that will feature heavily in the rules to be
	// created below
	raw_term tick({ concat(out_sym, "_tick"), elem_openp, elem_closep }),
		tock({ concat(out_sym, "_tock"), elem_openp, elem_closep }),
		fixpoint({ concat(out_sym, "_fixpoint"), elem_openp, timestep_var,
			next_timestep_var, elem_closep }),
		dec_databases({ concat(out_sym, "_databases"), elem_openp,
			timestep_var, name_var, params_var, elem_closep }),
		enc_databases({ concat(out_sym, "_databases"), elem_openp,
			elem(0), name_var, params_var, elem_closep });

	// Make variables for each head and tail in a linked list
	vector<elem> params_vars, param_vars;
	for(int_t i = 0; i < max_arity; i++) {
		params_vars.push_back(elem::fresh_var(dict));
		param_vars.push_back(elem::fresh_var(dict));
	}

	// Create rules to decode the contents of the interpreter's
	// database into a temporary relation on each tick
	for(int_t i = 0; i <= max_arity; i++) {
		vector<elem> decode_tmp_elems = { decode_tmp_rel,
			elem_openp, name_var };
		for(int_t j = 0; j < i; j++) {
			decode_tmp_elems.push_back(param_vars[j]);
		}
		decode_tmp_elems.push_back(elem_closep);
		raw_term decode_tmp_head(decode_tmp_elems);
		raw_rule decode_tmp_rule(decode_tmp_head, { fixpoint,
			dec_databases, tick });
		// Here we decode the number representing a list into its
		// various heads and tails
		elem current_params_var = params_var;
		for(int_t j = 0; j < i; j++) {
			decode_tmp_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_fst"), elem_openp, current_params_var,
					param_vars[j], elem_closep}));
			decode_tmp_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_rst"), elem_openp, current_params_var,
					params_vars[j], elem_closep}));
			current_params_var = params_vars[j];
		}
		decode_tmp_rule.b[0].push_back(raw_term(
			{concat(domain_sym, "_nil"), elem_openp, current_params_var,
				elem_closep}));
		// Add the temporary decoding rule
		rp.r.push_back(decode_tmp_rule);
		// Mark the temporary decoding rule as hidden
		rp.hidden_rels.insert(get_signature(decode_tmp_head));
	}

	// Prepare the rules that will clear the decoder and temporary
	// decoder relations
	raw_rule tock_clear;
	tock_clear.b = {{tock}};

	// Make a rule to copy the temporary decoder relation into the
	// decoder relation on each tock
	for(int_t i = 0; i <= max_arity; i++) {
		// Make the terms to capture a temporary decoder relation entry
		// and to insert a decoder relation entry
		vector<elem>
			decode_elems = { concat(codec_rel, "_decode"), elem_openp, name_var },
			decode_tmp_elems = { decode_tmp_rel, elem_openp, name_var };
		for(int_t j = 0; j < i; j++) {
			decode_elems.push_back(param_vars[j]);
			decode_tmp_elems.push_back(param_vars[j]);
		}
		decode_elems.push_back(elem_closep);
		decode_tmp_elems.push_back(elem_closep);
		raw_term decode_head(decode_elems),
			decode_tmp_head(decode_tmp_elems);
		// Make the rule to do the copying and add it to the program
		raw_rule decode_rule_add(decode_head, { decode_tmp_head, tock });
		raw_rule decode_rule_del(decode_head.negate(), { decode_tmp_head.negate(), tock });
		rp.r.push_back(decode_rule_add);
		rp.r.push_back(decode_rule_del);

		// Build up the rules that will clear the decoder and temporary
		// decoder relations
		tock_clear.h.push_back(decode_tmp_head.negate());
	}

	// Now add the clearing rule to the final program
	rp.r.push_back(tock_clear);

	// Make rules that take decoded terms and add them to the step 0
	// database of the given interpreter on each tock
	for(int_t i = 0; i <= max_arity; i++) {
		// The decoded terms will be coming from a <codec>_encode
		// relation
		vector<elem> encode_elems = { concat(codec_rel, "_encode"),
			elem_openp, name_var };
		for(int_t j = 0; j < i; j++) {
			encode_elems.push_back(param_vars[j]);
		}
		encode_elems.push_back(elem_closep);
		raw_term encode_head(encode_elems);
		// Make and add the rule that will add a decoded term of the
		// given arity into the step 0 database of the interpreter.
		raw_rule encode_rule(enc_databases, { encode_head, tock });
		// Make the group of terms that will compute the encoding of
		// the decoded tuple
		elem current_params_var = params_var;
		for(int_t j = 0; j < i; j++) {
			encode_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_fst"), elem_openp, current_params_var,
					param_vars[j], elem_closep}));
			encode_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_rst"), elem_openp, current_params_var,
					params_vars[j], elem_closep}));
			current_params_var = params_vars[j];
		}
		encode_rule.b[0].push_back(raw_term(
			{concat(domain_sym, "_nil"), elem_openp, current_params_var,
				elem_closep}));
		rp.r.push_back(encode_rule);
	}
	// Indicate success
	o::dbg() << "Generated codec for: " << drt << endl;
	return true;
}

/* Checks if the relation the first rule belongs to precedes the
 * relation that the second rule belongs to. A relation precedes another
 * relation if its name precedes the other relation's name. In the case
 * of a tie, a relation precedes another relation if its arity is lower
 * than the other's. */

bool rule_relation_precedes(const raw_rule &rr1, const raw_rule &rr2) {
	if(rr1.h[0].e[0] == rr2.h[0].e[0]) {
		return rr1.h[0].e.size() < rr2.h[0].e.size();
	} else {
		return rr1.h[0].e[0] < rr2.h[0].e[0];
	}
}

/* Convenience function for creating most general rule head for the
 * given relation. */

raw_term driver::relation_to_term(const rel_info &ri) {
	vector<elem> els = { get<0>(ri), elem_openp };
	for(int_t i = 0; i < get<1>(ri); i++) {
		els.push_back(elem::fresh_var(dict));
	}
	els.push_back(elem_closep);
	return raw_term(els);
}

/* Convenience function to condition the given rule with the given
 * condition term. */

raw_rule condition_rule(raw_rule rr, const raw_term &cond) {
	if(rr.b.empty()) {
		rr.b.push_back({cond});
	} else {
		for(vector<raw_term> &bodie : rr.b) {
			bodie.push_back(cond);
		}
	}
	return rr;
}

/* Rename the relations in the heads of the given rule to that given by
 * the supplied renaming map. */

raw_rule rename_rule(raw_rule rr, map<elem, elem> &rename_map) {
	for(raw_term &rt : rr.h) {
		auto jt = rename_map.find(rt.e[0]);
		if(jt != rename_map.end()) {
			rt.e[0] = jt->second;
		}
	}
	return rr;
}

/* Applies the given transformation to the given program in such a way
 * that it completes in a single step. Does this by separating the given
 * program into an execute and a writeback stage which serves to stop
 * the construction of the next database from interfering with the
 * execution of the current stage. */

void driver::step_transform(raw_prog &rp,
		const function<void(raw_prog &)> &f) {
	map<elem, elem> freeze_map;
	map<elem, elem> unfreeze_map;
	// Separate the internal rules used to execute the parts of the
	// transformation from the external rules used to expose the results
	// of computation.
	vector<raw_rule> int_prog;
	vector<raw_term> fact_prog;
	vector<raw_term> goal_prog;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(raw_rule rr : rp.r) {
		if(rr.type == raw_rule::GOAL) {
			// Separate out program goals as these are applied after
			// computation
			goal_prog.insert(goal_prog.end(), rr.h.begin(), rr.h.end());
			continue;
		}
		for(raw_term &rt : rr.h) {
			if(auto it = freeze_map.find(rt.e[0]); it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_temp_sym(dict);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			rp.hidden_rels.insert({ rt.e[0].e, rt.arity });
		}
		if(rr.is_fact() || rr.is_goal()) {
			// Separate out program facts as they need to be in database by
			// 0th step
			fact_prog.insert(fact_prog.end(), rr.h.begin(), rr.h.end());
		} else {
			int_prog.push_back(rr);
		}
	}
	// Apply the modifications from the above loop
	rp.r = int_prog;
	// Execute the transformation on the renamed rules.
	f(rp);

	// Partition the rules by relations
	typedef set<raw_rule> relation;
	map<rel_info, relation> rels;
	for(const raw_rule &rr : rp.r) {
		rels[get_relation_info(rr.h[0])].insert(rr);
	}
	map<const relation *, rel_info> rrels;
	for(const auto &[ri, r] : rels) {
		rrels[&r] = ri;
	}
	// Initialize the dependency lists
	map<const relation *, set<const relation *>> deps, rdeps;
	for(const auto &[k, v] : rels) {
		deps[&v] = {};
		rdeps[&v] = {};
	}
	// Make the adjacency lists based on rule dependency
	for(const auto &[k, v] : rels) {
		for(const raw_rule &rr : v) {
			for(const vector<raw_term> &bodie : rr.b) {
				for(const raw_term &rt : bodie) {
					rel_info target = get_relation_info(rt);
					if(rels.find(target) != rels.end()) {
						// Store the edges in both directions so that reverse
						// lookups are easy
						deps[&rels[target]].insert(&v);
						rdeps[&v].insert(&rels[target]);
					}
				}
			}
		}
	}
	// Topologically sort the relations
	vector<set<const relation *>> sorted;
	// Represents the relations that do not depend on other relations
	set<const relation *> current_level;
	for(const auto &[k, v] : rdeps) {
		if(v.empty()) {
			current_level.insert(k);
		}
	}
	// Kahn's algorithm: start from relations with no dependencies and
	// work our way up
	while(!current_level.empty()) {
		set<const relation *> next_level;
		for(const relation *n : current_level) {
			for(const relation *m : deps[n]) {
				rdeps[m].erase(n);
				if(rdeps[m].empty()) {
					next_level.insert(m);
				}
			}
			deps[n].clear();
		}
		sorted.push_back(current_level);
		current_level = next_level;
	}
	// If there are interdependencies between rules
	if(sorted.size() > 1) {
		rp.r.clear();
		// First add all the facts back into the sequenced program
		for(const raw_term &rt : fact_prog) {
			// If the fact is in a relation that is sequenced
			if(rels.find(get_relation_info(rt)) != rels.end()) {
				// Add it under its internal name, for we will create rule that
				// copies the internal relation to the external
				rp.r.push_back(raw_rule(rt));
			} else {
				// Add it under its external name because no rules will be
				// created to copy it
				rp.r.push_back(rename_rule(raw_rule(rt), unfreeze_map));
			}
		}
		// At each stage of TML execution, exactly one of the nullary facts
		// in this vector are asserted
		vector<elem> clock_states = { elem::fresh_temp_sym(dict) };
		// Push the internal rules onto the program using conditioning to
		// control execution order
		for(const set<const relation *>& v : sorted) {
			// Make a new clock state for the current stage
			const elem clock_state = elem::fresh_temp_sym(dict);
			// If the previous state is asserted, then de-assert it and assert
			// this state
			rp.r.push_back(raw_rule(raw_term(clock_state, vector<elem>{}),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
			rp.r.push_back(raw_rule(raw_term(clock_states.back(), vector<elem>{}).negate(),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
			clock_states.push_back(clock_state);

			for(const relation *w : v) {
				raw_term general_head = relation_to_term(rrels[w]);
				// If the present relation does not correspond to a relation in
				// the original program, then clear the table so it does not
				// affect future stages.
				if(unfreeze_map.find(general_head.e[0]) == unfreeze_map.end()) {
					rp.r.push_back(raw_rule(general_head.negate(),
						{ general_head, raw_term(clock_states[0], vector<elem>{}) }));
				} else {
					// Update the external interface during the writeback stage
					// by copying the contents of the final temporary relation
					// back to the external interface.
					raw_term original_head = general_head;
					original_head.e[0] = unfreeze_map[general_head.e[0]];
					original_head.neg = general_head.neg = true;
					rp.r.push_back(condition_rule(raw_rule(original_head, general_head),
						raw_term(clock_states[0], vector<elem>{})));
					original_head.neg = general_head.neg = false;
					rp.r.push_back(condition_rule(raw_rule(original_head, general_head),
						raw_term(clock_states[0], vector<elem>{})));
				}
				for(raw_rule rr : *w) {
					// Condition everything in the current stage with the same
					// clock state
					rp.r.push_back(condition_rule(rr,
						raw_term(clock_state, vector<elem>{})));
				}
			}
		}
		// Start the clock ticking by asserting stage0, asserting stage1
		// if stage0 holds, and asserting the clock if stage0 holds but
		// stage1 does not.
		raw_term stage0(elem::fresh_temp_sym(dict), vector<elem>{});
		raw_term stage1(elem::fresh_temp_sym(dict), vector<elem>{});
		raw_term stage2(clock_states[0], vector<elem>{});
		rp.r.push_back(raw_rule(stage0));
		rp.r.push_back(raw_rule(stage1, stage0));
		rp.r.push_back(raw_rule(stage2, {stage0, stage1.negate()}));

		// Hide the clock states
		rp.hidden_rels.insert({ stage0.e[0].e, stage0.arity });
		rp.hidden_rels.insert({ stage1.e[0].e, stage1.arity });
		for(const elem &clock_state : clock_states) {
			rp.hidden_rels.insert({ clock_state.e, {0} });
		}

		if(clock_states.size() > 1) {
			// If the previous state is asserted, then de-assert it and assert
			// this state
			rp.r.push_back(raw_rule(raw_term(clock_states[0], vector<elem>{}),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
			rp.r.push_back(raw_rule(raw_term(clock_states.back(), vector<elem>{}).negate(),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
		}
	} else {
		// Add all program facts back
		for(const raw_term &rt : fact_prog) {
			rp.r.push_back(raw_rule(rt));
		}
		// If there are no interdepencies then we can just restore the
		// original rule names to the transformed program
		for(raw_rule &rr : rp.r) {
			rr = rename_rule(rr, unfreeze_map);
		}
	}
	// Add all program goals back
	for(const raw_term &rt : goal_prog) {
		rp.r.push_back(raw_rule(raw_rule::GOAL, rt));
	}
}

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
			t.l->el = renames[ovar] = gen(ovar);
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

/* Returns the difference between the two given sets. I.e. the second
 * set removed with multiplicity from the first. */

set<elem> set_difference(const multiset<elem> &s1,
		const set<elem> &s2) {
	set<elem> res;
	set_difference(s1.begin(), s1.end(), s2.begin(), s2.end(),
		inserter(res, res.end()));
	return res;
}

/* Returns the intersection of the two given sets. I.e. all the elems
 * that occur in both sets. */

set<elem> set_intersection(const set<elem> &s1, const set<elem> &s2) {
	set<elem> res;
	set_intersection(s1.begin(), s1.end(), s2.begin(), s2.end(),
		inserter(res, res.end()));
	return res;
}

/* Iterate through the FOL rules and remove the outermost existential
 * quantifiers. Required because TML to DNF conversion assumes that quantifier
 * variables are only visible within their bodies. */

void driver::export_outer_quantifiers(raw_prog &rp) {
	for(raw_rule &rr : rp.r) {
		if(rr.is_form()) {
			sprawformtree prft = make_shared<raw_form_tree>(*rr.prft);
			// Repeatedly strip outermost existential quantifier
			while (prft->type == elem::EXISTS) prft = prft->r;
			// Now export the outermost existentially quantified variables if their
			// values are needed outside the particular quantifications. First
			// determine if export is required.
			bool export_required = false;
			set<elem> used_vars = collect_free_vars({rr.h});
			raw_form_tree *pprft = &*rr.prft;
			for(; pprft->type == elem::EXISTS || pprft->type == elem::UNIQUE;
					pprft = &*pprft->r) {
				if(used_vars.find(*pprft->l->el) != used_vars.end()) {
					// Export is required if the quantification variable is used outside
					// this quantifiers scope
					export_required = true;
				} else {
					used_vars.insert(*pprft->l->el);
				}
			}
			if(export_required) {
				// Now conjunct the rule formula with a copy of what is inside the
				// existential quantifiers so that variables can be exported whilst
				// uniqueness constraints are still being enforced.
				rr.prft = raw_form_tree(elem::AND, make_shared<raw_form_tree>(*pprft), prft);
			}
		}
	}
}

/* Rules with multiple heads are also converted to multiple rules with
 * single heads. */

void driver::split_heads(raw_prog &rp) {
	// Split rules with multiple heads and delete those with 0 heads
	for(auto it = rp.r.begin(); it != rp.r.end();) {
		if(it->h.size() != 1) {
			// 0 heads are effectively eliminated, and multiple heads are
			// split up.
			const raw_rule rr = *it;
			it = rp.r.erase(it);
			for(const raw_term &rt : rr.h) {
				raw_rule nr = rr;
				nr.h = { rt };
				it = rp.r.insert(it, nr);
			}
		} else {
			// Leave the single-headed rules alone.
			it++;
		}
	}
}

/* If the given term belongs to a hidden relation, record its relation
 * in signatures and record the given rule's dependency on this term's
 * relation. */

void record_hidden_relation(const raw_prog &rp, raw_rule &rr,
		const raw_term &rt, set<signature> &signatures,
		map<signature, set<raw_rule *>> &dependants) {
	if(rt.extype == raw_term::REL) {
		if(signature sig = get_signature(rt); has(rp.hidden_rels, sig)) {
			dependants[sig].insert(&rr);
			signatures.insert(sig);
		}
	}
}

/* Update the variable usage map by 1 (2) (see below) for each distinct variable
 * occuring in the given positive (negative) term. Record the distinct variables
 * in the given pointer if it is not null. Note that the update is 2 for
 * symbols as they are treated as a unique variable with a separate
 * equality contraint to fix it to a particular symbol. Note also that the
 * update is 2 for negative terms because its variables may create additional
 * ways for the given rule to be satisfied. I.e. removing a variable occuring
 * once in a negative term would cause the nature of the program's solutions to
 * change. */

void record_variable_usage(const raw_term &rt,
		map<elem, int_t> &var_usages, set<elem> *relevant_vars) {
	set<elem> unique_vars;
	for(const elem &e : rt.e) unique_vars.insert(e);
	signature body_signature = get_signature(rt);
	if(relevant_vars)
		for(const elem &e : rt.e) relevant_vars->insert(e);
	for(const elem &e : unique_vars)
		var_usages[e] += ((e.type == elem::VAR) && !rt.neg) ? 1 : 2;
}

/* There are four kinds of rules to deal with: those in which the
 * signature being modified occurs only within the body, those in which
 * it occurs only within the head, and those within which it occurs in
 * both. If it only occurs in the head, then the use of each head
 * variable should be 0/1, as this would allow all the head variables to
 * be eliminated without affecting computation. If it only occurs in the
 * body, then the use of each variable occuring in terms of the
 * signature being modified should be set to the number of separate
 * terms that use the variable. This way all those variables occuring
 * only in one term and hence do not affect the satisfiability of the
 * current rule nor the derived term can be eliminated. If it occurs in
 * both, then the occurence of variables in the head can be ignored
 * because this does not affect the rule's satisfiability and because we
 * want these variables to be eliminatable. However the number of
 * separate terms the variables occuring in terms corresponding to the
 * signature under modification should still be recorded as this does
 * affect satisfiability. */

ints calculate_variable_usage(const signature &sig,
		const map<signature, set<raw_rule *>> &dependants) {
	// This variable stores the number of separate terms each
	// position of the given relation is simultaneously used in.
	// Important for determining whether a given position is
	// eliminatable.
	ints uses(sig.second[0], 1);
	// The eliminatability of a relation position is entirely
	// determined by how it is used in the rules that depend on its
	// relation
	for(const raw_rule *rr : dependants.at(sig)) {
		map<elem, int_t> var_usages;
		// Record the variables occuring in the head if the head
		// relation is distinct from the one currently being modified.
		// Variable exportation would prevent us from deleting this
		// variable in the body.
		const raw_term &head = rr->h[0];
		const signature &head_signature = get_signature(head);
		if(sig != head_signature)
			record_variable_usage(head, var_usages, nullptr);
		// The set of all the variables use by terms of this relation
		// occuring in the body. If no such terms exist, then the term
		// of this relation must occur in the head, in which case every
		// position of this relation could be eliminatable.
		set<elem> relevant_vars;
		// Now record also the number of separate conjuncts each variable occurs in
		// whilst populating relevant_vars according to its specification. Note that
		// the negative heads are treated as additional body conjuncts.
		set<raw_term> bodie;
		if(!rr->b.empty()) bodie.insert(rr->b[0].begin(), rr->b[0].end());
		if(head.neg) bodie.insert(head.negate());
		for(const raw_term &rt : bodie)
			record_variable_usage(rt, var_usages,
				get_signature(rt) == sig ? &relevant_vars : nullptr);
		// Now eliminate the irrelevant variables. These are the
		// variables that do not affect the current rule's
		// satisfiability through terms of the relation currently being
		// minimized.
		if(sig == head_signature)
			for(auto &[var, count] : var_usages)
				if(!has(relevant_vars, var)) count = 0;
		// Now assign the most pessimistic variable usages to each position
		// in the signature under modification.
		if(head.extype == raw_term::REL && sig == head_signature)
			for(size_t i = 0; i < head.e.size() - 3; i++)
				uses[i] = max(uses[i], var_usages[head.e[i+2]]);
		for(const raw_term &rt : bodie)
			if(rt.extype == raw_term::REL && sig == make_pair(rt.e[0].e, rt.arity))
				for(size_t i = 0; i < rt.e.size() - 3; i++)
					uses[i] = max(uses[i], var_usages[rt.e[i+2]]);
	}
	return uses;
}

/* Delete the elements of the given term that have a usage of equal to
 * one if the term's signature equals the one supplied. Otherwise if
 * there is a usage equal to one, then add the term's signature to
 * pending because it may have a contraction after the given signature
 * is done. */

void contract_term(raw_term &rt, const elem &new_rel, const ints &uses,
		const signature &sig, set<signature> &pending_signatures,
		raw_prog &rp) {
	if(rt.extype == raw_term::REL &&
			find(uses.begin(), uses.end(), 1) != uses.end()) {
		signature body_signature = get_signature(rt);
		if(sig == body_signature) {
			rt.e[0] = new_rel;
			for(int_t i = uses.size() - 1; i >= 0; i--)
				if(uses[i] == 1) rt.e.erase(rt.e.begin() + 2 + i);
			rt.calc_arity(nullptr);
			if(auto it = pending_signatures.find(sig); it != pending_signatures.end()) {
				pending_signatures.erase(it);
				pending_signatures.insert(get_signature(rt));
			}
		} else if(has(rp.hidden_rels, body_signature)) {
			pending_signatures.insert(body_signature);
		}
	}
}

void collect_free_vars(const vector<vector<raw_term>> &b,
		vector<elem> &bound_vars, set<elem> &free_vars) {
	for(const vector<raw_term> &bodie : b) {
		for(const raw_term &rt : bodie) {
			collect_free_vars(rt, bound_vars, free_vars);
		}
	}
}

set<elem> collect_free_vars(const vector<vector<raw_term>> &b) {
	vector<elem> bound_vars;
	set<elem> free_vars;
	collect_free_vars(b, bound_vars, free_vars);
	return free_vars;
}

/* Collect all the variables that are free in the given rule. */

void collect_free_vars(const raw_rule &rr, set<elem> &free_vars) {
	vector<elem> bound_vars = {};
	for(const raw_term &rt : rr.h) {
		collect_free_vars(rt, bound_vars, free_vars);
	}
	if(rr.is_form()) {
		collect_free_vars(*rr.prft, bound_vars, free_vars);
	} else {
		collect_free_vars(rr.b, bound_vars, free_vars);
	}
}

set<elem> collect_free_vars(const raw_rule &rr) {
	set<elem> free_vars;
	collect_free_vars(rr, free_vars);
	return free_vars;
}

/* Collect all the variables that are free in the given term. */

set<elem> collect_free_vars(const raw_term &t) {
	set<elem> free_vars;
	vector<elem> bound_vars = {};
	collect_free_vars(t, bound_vars, free_vars);
	return free_vars;
}

void collect_free_vars(const raw_term &t, vector<elem> &bound_vars,
		set<elem> &free_vars) {
	set<elem> term_vars;
	// Get all the variables used in t
	collect_vars(t, term_vars);
	// If the variable is bound by some quantifier, then it cannot be free
	for(const elem &bv : bound_vars) term_vars.erase(bv);
	// Now term_vars only has free variables; add those to free_vars
	for(const elem &tv : term_vars) free_vars.insert(tv);
}

/* Collect all the variables that are free in the given tree. */

set<elem> collect_free_vars(const raw_form_tree &t) {
	set<elem> free_vars;
	vector<elem> bound_vars = {};
	collect_free_vars(t, bound_vars, free_vars);
	return free_vars;
}

void collect_free_vars(const raw_form_tree &t, vector<elem> &bound_vars,
		set<elem> &free_vars) {
	switch(t.type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			collect_free_vars(*t.l, bound_vars, free_vars);
			collect_free_vars(*t.r, bound_vars, free_vars);
			break;
		case elem::NOT:
			collect_free_vars(*t.l, bound_vars, free_vars);
			break;
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			elem elt = *(t.l->el);
			bound_vars.push_back(elt);
			collect_free_vars(*t.r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} case elem::NONE: {
			collect_free_vars(*t.rt, bound_vars, free_vars);
			break;
		} default:
			assert(false); //should never reach here
	}
}

// ----------------------------------------------------------------------------
// transformations handler
bool driver::transform(raw_prog& rp, const strs_t& /*strtrees*/) {

	auto get_vars = [this](const raw_term& t) {
		for (const elem& e : t.e)
			if (e.type == elem::VAR)
				vars.insert(e.e);
	};
	auto get_all_vars = [get_vars](const raw_prog& p) {
		for (const raw_rule& r : p.r) {
			for (const raw_term& t : r.h) get_vars(t);
			for (const vector<raw_term>& b : r.b)
				for (const raw_term& t : b)
					get_vars(t);
		}
	};
	get_all_vars(rp);

	// TODO this is sort of cache to not optimize same program twice
	// but this situation might become evident earlier, i.e if same file is
	// passed as input twice.
	static set<raw_prog *> transformed_progs;
	if(transformed_progs.find(&rp) != transformed_progs.end()) return true;
	transformed_progs.insert(&rp);

	// If we want proof trees, then we need to transform the productions into
	// rules first since only rules are supported by proof trees.
	if(opts.enabled("strgrammar")) {
		DBG(o::transformed() <<
			"Transforming Grammar ...\n" << endl;)
		for (auto x : pd.strs)
			if (!has(transformed_strings, x.first))
				transform_string(x.second, rp, x.first),
				transformed_strings.insert(x.first);
		if (!rp.g.empty()) {
			if (pd.strs.size() > 1)
				return throw_runtime_error(err_one_input);
			else transform_grammar(rp, pd.strs.begin()->first,
				pd.strs.begin()->second.size());
			rp.g.clear();
		}
		DBG(o::transformed() <<
			"Transformed Grammar:\n\n" << rp << endl;)
	}
	return true;
}

bool driver::transform_handler(raw_prog &p) {

	// Split heads are a prerequisite to safety checking
	split_heads(p);

#ifdef TYPE_RESOLUTION
	raw_prog tr = ir->generate_type_resolutor(p.nps[0]);
	rt_options to;
	to.binarize = false;
	to.bproof = proof_mode::none;
	to.fp_step = opts.enabled("fp");  //disables "__fp__()."
	to.optimize  = false;
	to.print_binarized = false;
	to.show_hidden = false;

	ir_builder ir_handler(dict, to);
	tables tbl_int(to, bltins);

	ir_handler.dynenv = &tbl_int;
	ir_handler.printer = &tbl_int;
	ir_handler.dynenv->bits = 2;

	tables_progress tp(dict, *ir);
	if (!run_prog(tr, strs_t(), 0,0, tp, to, tbl_int, ir_handler)) return false;

	for(const term &el : tbl_int.decompress()) {
		DBG(COUT << el << endl;); //this line fails in release
		sig s = ir_handler.to_native_sig(el);
		ir->append(ir->relid_argtypes_map, s);
	}
	ir_handler.dynenv->bits = 0;
	ir->type_resolve(p.nps[0]);
#endif

	if (opts.enabled("safecheck")) {
		raw_prog temp_rp(p); //temporary fix to safecheck
		if(auto res = is_safe(temp_rp.nps[0])) {
			ostringstream msg;
			// The program is unsafe so inform the user of the offending rule
			// and variable.
			msg << "The variable "<< res->first <<" of " <<
					res->second << " is not limited. "
					"Try rewriting the rule to make its "
					"safety clearer.";
			return error = true, parse_error(msg.str().c_str());
		}
	}

	DBG(if (opts.enabled("transformed"))
		o::transformed() << "Pre-Transforms Prog:\n" << p << endl;);

	if (!transform(p, pd.strs)) return false;
	for (auto& np : p.nps)
		if (!transform(np, pd.strs)) return false;

	if (opts.enabled("state-blocks"))
    	transform_state_blocks(p, {});
	else if (raw_prog::require_state_blocks)
		return error = true,
				throw_runtime_error("State blocks require "
					"-sb (-state-blocks) option enabled.");

	if (opts.disabled("fp-step") && raw_term::require_fp_step)
		return error = true,
			throw_runtime_error("Usage of the __fp__ term requires "
				"--fp-step option enabled.");

	//NOTE: guards is assuming empty rules with single nps at top
	if (opts.enabled("guards")) {
		ir->transform_guards(p);
		if (opts.enabled("transformed")) o::to("transformed")
				<< "# after transform_guards:\n" << p << endl << endl;
	} else if (raw_prog::require_guards)
		return error = true,
				throw_runtime_error("Conditional statements require "
						"-g (-guards) option enabled.");

#ifdef BIT_TRANSFORM
	ir->bit_transform(p.nps[0], opts.get_int("bitorder"));

#endif

	DBG(if (opts.enabled("transformed"))
		o::to("transformed") << "Post-Transforms Prog:\n" << p << endl;);

	return true;
}

void driver::recursive_transform(raw_prog &rp/*, const function<bool (raw_prog &rp)> &f*/) {
	for(raw_prog &np : rp.nps) {
		recursive_transform(np);
		if (!transform_handler(np)) assert(false);
	}
}
//-----------------------------------------------------------------------------
// execution control
void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::step(size_t steps, size_t break_on_step) {
	return run(steps, break_on_step);
}

bool driver::run(size_t steps, size_t break_on_step) {
	if (!running) restart();
	if (opts.disabled("run") && opts.disabled("repl")) return true;

	size_t step = nsteps();
	raw_prog::last_id = 0; // reset rp id counter;

	clock_t start, end;
	measure_time_start();

	tables_progress tp(dict, *ir);
	rt_options rt;

	if (opts.enabled("guards"))
		// guards transform, will lead to !root_empty
		result = run_prog(rp.p, pd.strs, steps, break_on_step, tp, rt, *tbl);
	else if (rp.p.nps.size())
		result = run_prog((rp.p.nps)[0], pd.strs, steps, break_on_step, tp, rt, *tbl);
	else
		result = false;

	o::ms() << "# elapsed: ", measure_time_end();

	if (tbl->error) error = true;
	pd.elapsed_steps = nsteps() - step;
	return result;
}

// ----------------------------------------------------------------------------

bool driver::add(input* in) {
	//TODO: handle earlier errors on the input arguments
#ifdef NEEDS_REWRITE
	if (opts.enabled("earley")) {
		parse_tml(in, rp);
#ifdef DEBUG
		raw_progs rpt(dict);
		rpt.parse(in);
		o::inf() << "\n### parsed by earley:   >\n" << rp << "<###\n";
		o::inf() << "\n### parsed the old way: >\n" << rpt << "<###\n";
		stringstream s1, s2;
		s1 << rp;
		s2 << rpt;
		if (s1.str() != s2.str()) o::inf() << "\n\tNO MATCH\n";
#endif
	} else 	//TODO: lex here
#endif
		if (in->error | !rp.parse(in)) return !(error = true);
	return true;
}

void driver::read_inputs() {
	current_input = ii->first();
	if (current_input && !add(current_input)) return;
	while (current_input && current_input->next()) {
		current_input = current_input->next();
		if (!add(current_input)) return;
		++current_input_id;
	}
}

void driver::init_tml_update(updates& updts) {
	updts.rel_tml_update = dict.get_rel(dict.get_lexeme("tml_update"));
	updts.sym_add = dict.get_sym(dict.get_lexeme("add"));
	updts.sym_del = dict.get_sym(dict.get_lexeme("delete"));
}

bool driver::add_prog_wprod(flat_prog m, const vector<production>& g/*, bool mknums*/, tables &tbls, rt_options &rt, ir_builder &ir_handler) {

	DBG(o::dbg() << "add_prog_wprod" << endl;);
	error = false;
	tables::clear_memos();

	updates updts;
	// TODO this should be part of rt_options
	if (tbls.populate_tml_update) init_tml_update(updts);

	tbls.rules.clear(), tbls.datalog = true;

	// TODO this call must be done in the driver
	if (!ir_handler.transform_grammar(g, m)) return false;

	if (!tbls.get_rules(m)) return false;

	// filter for rels starting and ending with __
	auto filter_internal_tables = [] (const lexeme& l) {
		size_t len = l[1] - l[0];
		return len > 4 && '_' == l[0][0]     && '_' == l[0][1] &&
				  '_' == l[0][len-2] && '_' == l[0][len-1];
	};

	// TODO clarify difference between hidden and internal. Anyway, this
	// problem would disappear once we refactor run methods.
	ints internal_rels = dict.get_rels(filter_internal_tables);
	for (auto& tbl : tbls.tbls)
		for (int_t rel : internal_rels)
			if (rel == tbl.s.first) { tbl.hidden = true; break; }

	if (rt.optimize) bdd::gc();
	return true;
}

bool driver::run_prog_wedb(const std::set<raw_term> &edb, raw_prog rp,
	dict_t &dict, builtins& bltins, const options &opts, std::set<raw_term> &results,
	progress& p) {
	std::map<elem, elem> freeze_map, unfreeze_map;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(int_t i = rp.r.size() - 1; i >= 0; i--) {
		for(raw_term &rt : rp.r[i].h) {
			raw_term rt2 = rt;
			auto it = freeze_map.find(rt.e[0]);
			if(it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_temp_sym(dict);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			rp.r.push_back(raw_rule(rt2, rt));
		}
	}
	// Now add the extensional database to the given program.
	for(const raw_term &rt : edb) {
		rp.r.push_back(raw_rule(rt));
	}
	// Run the program to obtain the results which we will then filter
	std::set<raw_term> tmp_results;
	rt_options to;
	to.apply_regexpmatch = opts.enabled("regex");
	to.bitorder          = opts.get_int("bitorder");
	to.bproof            = proof_mode::none;
	to.fp_step           = opts.enabled("fp");
	to.optimize          = opts.enabled("optimize");
	to.print_transformed = opts.enabled("t");

	tables tbl(to, bltins);
	strs_t strs;
	driver drv(opts);
	if (!drv.run_prog(rp, strs, 0, 0, p, to, tbl)) return false;
	for(const term &result : tbl.decompress())
		tmp_results.insert(drv.ir->to_raw_term(result));

	// Filter out the result terms that are not derived and rename those
	// that are derived back to their original names.
	for(raw_term res : tmp_results) {
		auto jt = unfreeze_map.find(res.e[0]);
		if(jt != unfreeze_map.end()) {
			res.e[0] = jt->second;
			results.insert(res);
		}
	}
	return true;
}

bool driver::run_prog(const raw_prog& p, const strs_t& strs_in, size_t steps,
	size_t break_on_step, progress& ps, rt_options& rt, tables &tbls, ir_builder &ir_handler) {
	DBG(o::dbg() << "run_prog" << endl;);
	clock_t start{}, end;
	double t;
	if (rt.optimize) measure_time_start();

	flat_prog fp = ir_handler.to_terms(p);
	#ifdef FOL_V2
	print(o::out() << "FOF flat_prog:\n", fp) << endl;
	#endif // FOL_V2

	ir_handler.load_strings_as_fp(fp, strs_in);

	ir_handler.syms = dict.nsyms();

	#if defined(BIT_TRANSFORM) | defined(BIT_TRANSFORM_V2)
		tbls.bits = 1;
	#else
		#ifdef TYPE_RESOLUTION
		size_t a = max(max(ir_handler.nums, ir_handler.chars), ir_handler.syms);
		if (a == 0) tbls.bits++;
		else while (a > size_t (1 << tbls.bits)-1) tbls.bits++;
		#else
		while (max(max(ir_handler.nums, ir_handler.chars), ir_handler.syms) >= (1 << (tbls.bits - 2))) // (1 << (bits - 2))-1
			tbls.add_bit();
		#endif
	#endif // BIT_TRANSFORM | BIT_TRANSFORM_V2

	// Calling optimizations methods if requested
	auto ofp = optimize(fp);
	// auto ofp = fp;

	#ifdef DEBUG
	print(o::dbg() << "Final optimized flat_prog:\n", ofp) << endl;
	#endif // DEBUG

	if (!add_prog_wprod(ofp, p.g, tbls, rt, ir_handler)) return false;

	//----------------------------------------------------------
	if (tbls.opts.optimize) {
		end = clock(), t = double(end - start) / CLOCKS_PER_SEC;
		o::ms() << "# pfp: " << endl; measure_time_start();
	}

	nlevel begstep = tbls.nstep;

	bool r = true;
	// run program only if there are any rules
	if (tbls.rules.size()) {
		tbls.fronts.clear();
		r = tbls.pfp(steps ? tbls.nstep + steps : 0, break_on_step, ps);
	} else {
		bdd_handles l = tbls.get_front();
		tbls.fronts = {l, l};
	}
	//----------------------------------------------------------
	//TODO: prog_after_fp is required for grammar/str recognition,
	// but it should be restructured
	if (r && tbls.prog_after_fp.size()) {
		if (!add_prog_wprod(tbls.prog_after_fp, {}, tbls, rt, ir_handler)) return false;
		r = tbls.pfp(0, 0, ps);
	}

	o::dbg() << "Tables bits: " << tbls.bits << "\n";
//	for (auto& t: tbls.tbls) print(o::dbg() << "Table: ", t);

	size_t went = tbls.nstep - begstep;
	if (r && p.nps.size()) { // after a FP run the seq. of nested progs
		for (const raw_prog& np : p.nps) {
			steps -= went; begstep = tbls.nstep;
			rt_options rt;
			r = run_prog(np, strs_in, steps, break_on_step, ps, rt, tbls, ir_handler);
			went = tbls.nstep - begstep;
			if (!r && went >= steps) {
				//assert(false && "!r && went >= steps");
				break;
			}
		}
	}

	if (tbls.opts.optimize)
		(o::ms() <<"# add_prog: "<< t << " pfp: "), measure_time_end();
	return r;
}

void add_print_updates_states(const std::set<std::string> &tlist, tables &tbls, ir_builder *ir_handler, dict_t &dict) {
	for (const std::string& tname : tlist)
		tbls.opts.pu_states.insert(ir_handler->get_table(
				ir_handler->get_sig(dict.get_lexeme(tname), {0})));
}

template <typename T>
basic_ostream<T>& driver::print(basic_ostream<T>& os, const vector<term>& v) const {
	os << ir->to_raw_term(v[0]);
	if (v.size() == 1) return os << '.';
	os << " :- ";
	for (size_t n = 1; n != v.size(); ++n) {
		if (v[n].goal) os << '!';
		os << ir->to_raw_term(v[n]) << (n == v.size() - 1 ? "." : ", ");
	}
	return os;
}
template basic_ostream<char>& driver::print(basic_ostream<char>&, const vector<term>&) const;
template basic_ostream<wchar_t>& driver::print(basic_ostream<wchar_t>&, const vector<term>&) const;

template <typename T>
basic_ostream<T>& driver::print(basic_ostream<T>& os, const flat_prog& p) const{
	for (const auto& x : p)
		print(os << (x[0].tab == -1 ? 0 : tbl->tbls[x[0].tab].priority) <<
			'\t', x) << endl;
	return os;
}
template basic_ostream<char>& driver::print(basic_ostream<char>&, const flat_prog&) const;
template basic_ostream<wchar_t>& driver::print(basic_ostream<wchar_t>&, const flat_prog&) const;

driver::driver(string s, const options &o) : dict(dict_t()), opts(o), rp(raw_progs(dict)) {
	if (opts.error) { error = true; return; }


	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());
	if (!ii) return;
	if (s.size()) opts.parse(strings{ "-ie", s });

	rt_options to;
	if(auto proof_opt = opts.get("proof"))
		to.bproof = proof_opt->get_enum(map<string, enum proof_mode>
			{{"none", proof_mode::none},
			{"tree", proof_mode::tree},
			{"forest", proof_mode::forest_mode},
			{"partial-tree", proof_mode::partial_tree},
			{"partial-forest", proof_mode::partial_forest}});
	to.optimize          = opts.enabled("optimize");
	to.print_transformed = opts.enabled("t");
	to.apply_regexpmatch = opts.enabled("regex");
	to.fp_step           = opts.enabled("fp");
	to.show_hidden       = opts.enabled("show-hidden");
	to.bin_lr            = opts.enabled("bin-lr");
	to.bitorder          = opts.get_int("bitorder");
	to.incr_gen_forest	 = opts.enabled("incr-gen-forest");

	ir = new ir_builder(dict, to);
	builtins_factory* bf = new builtins_factory(dict, *ir);
	bltins = bf
		->add_basic_builtins()
		.add_bdd_builtins()
		.add_print_builtins()
		.add_js_builtins().bltins;
	tbl = new tables(to, bltins);

	ir->dynenv  = tbl;
	ir->printer = tbl;

	// TODO move this options to rt_options
	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	add_print_updates_states(opts.pu_states, *tbl, ir, dict);

	if (to.fp_step) ir->get_table(ir->get_sig(dict.get_lexeme("__fp__"), { 0 }));
	set_populate_tml_update(opts.enabled("tml_update"));
	set_regex_level(opts.get_int("regex-level"));

	read_inputs();

	raw_term raw_t;
	raw_t.arity = { 0 };
	raw_t.e.emplace_back(elem::SYM, dict.get_lexeme(string("__fp__")));
	tbl->fixed_point_term = ir->from_raw_term(raw_t);

	if (!error && !rp.p.nps.empty()) {
		directives_load((rp.p.nps)[0]);
		transform_handler(rp.p);
		// TODO review how recursion to nested programs should be handled per
		// transform vs globally recursive_transform(rp-p)
		if (opts.enabled("program-gen")) {
			string pname;
			cpp_gen g;
			g.gen(o::to("program-gen"), pname, rp) <<
				"\nauto& program_gen = " << pname << ";\n";
		}
	}
}

driver::driver(FILE *f, const options &o) : driver(input::file_read_text(f),o){}
driver::driver(string_t s, const options& o)    : driver(to_string(s), o) {}
driver::driver(const char *s, const options &o) : driver(string(s), o) {}
driver::driver(ccs   s, const options &o)       : driver(string_t(s), o) {}
driver::driver(const options &o)                : driver(string(), o) {}
driver::driver(string s)                        : driver(s, options()) {}
driver::driver(FILE *f)                         : driver(f, options()) {}
driver::driver(string_t s)                      : driver(to_string(s)) {}
driver::driver(const char *s)                   : driver(s, options()) {}
driver::driver(ccs s)                           : driver(string_t(s)) {}

driver::~driver() {
	if (tbl) delete tbl;
	if (ir) delete ir;
}

// ----------------------------------------------------------------------------

template <typename T>
void driver::list(std::basic_ostream<T>& os, size_t /*n*/) {
	os << rp.p << endl;
}
template void driver::list(std::basic_ostream<char>&, size_t);
template void driver::list(std::basic_ostream<wchar_t>&, size_t);

template <typename T>
void driver::info(std::basic_ostream<T>& os) {
	os<<"# step:      \t" << nsteps() <<" - " << pd.start_step <<" = "
		<< (nsteps() - pd.start_step) << " ("
		<< (running ? "" : "not ") << "running)" << endl;
	bdd::stats(os<<"# bdds:     \t")<<endl;
}
template void driver::info(std::basic_ostream<char>&);
template void driver::info(std::basic_ostream<wchar_t>&);

} // idni namespace
