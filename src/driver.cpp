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

#include "driver.h"
#include "err.h"
#include "cpp_gen.h"

#ifdef __EMSCRIPTEN__
#include "../js/embindings.h"
#endif 

using namespace std;

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
//			if (it == s.end()) parse_error(err_len, r.e[n+2].e);
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
		case directive::STDIN: return move(pd.std_input);
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
		//case directive::EVAL: transform_evals(p, d); break;
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
/*		case directive::STDOUT: pd.out.push_back(get_term(d.t,pd.strs));
					break;
		case directive::TREE:
			rel = dict.get_rel(d.t.e[0].e);
			if (has(pd.strtrees, rel) || has(pd.strs, rel))
				parse_error(err_str_defined, d.t.e[0].e);
			else pd.strtrees.emplace(rel, get_term(d.t,pd.strs));
			break;*/
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
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	switch(t.type) {
		case elem::IMPLIES:
			// Process the expanded formula instead
			return is_limited(var, expand_formula_node(t, d), wrt, scopes);
		case elem::COIMPLIES:
			// Process the expanded formula instead
			return is_limited(var, expand_formula_node(t, d), wrt, scopes);
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
						make_shared<raw_form_tree>(expand_formula_node(*t.l, d))), wrt, scopes);
				} case elem::COIMPLIES: {
					// Process the expanded formula instead
					return is_limited(var, raw_form_tree(elem::NOT,
						make_shared<raw_form_tree>(expand_formula_node(*t.l, d))), wrt, scopes);
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
						make_shared<raw_form_tree>(expand_formula_node(*t.l, d))), wrt, scopes);
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
			return is_limited(var, expand_formula_node(t, d), wrt, scopes);
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
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	switch(t.type) {
		case elem::IMPLIES:
			// Process the expanded formula instead
			return all_quantifiers_limited(expand_formula_node(t, d), scopes);
		case elem::COIMPLIES:
			// Process the expanded formula instead
			return all_quantifiers_limited(expand_formula_node(t, d), scopes);
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
			return all_quantifiers_limited(expand_formula_node(t, d), scopes);
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

/* Checks if the rule has a single head and a body that is either a tree
 * or a non-empty DNF. Second order quantifications and builtin terms
 * are not supported. */

bool is_query (const raw_rule &rr) {
	// Ensure that there are no multiple heads
	if(rr.h.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is either a tree or non-empty DNF
	if(!(rr.is_dnf() || rr.is_form())) return false;
	// Ensure that there is no second order quantification or builtins in
	// the tree
	raw_form_tree prft = *rr.get_prft();
	if(!prefold_tree(prft, true,
			[&](const raw_form_tree &t, bool acc) -> bool {
				return acc && (t.type != elem::NONE ||
					t.rt->extype != raw_term::BLTIN) && t.type != elem::SYM;}))
		return false;
	return true;
}

/* If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. */

bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t d;
	// Check that rules have correct format
	if(is_cq(rr1) && is_cq(rr2) &&
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
		for(const raw_term &res : results) {
			if(res == frozen_rr1.h[0]) {
				// If the frozen head is found, then there is a homomorphism
				// between the two rules.
				o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
				return true;
			}
		}
		// If no frozen head found, then there is no homomorphism.
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
		return false;
	} else {
		return false;
	}
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

	if(is_cq(rr1) && is_cq(rr2)) {
		o::dbg() << "Searching for homomorphisms from " << rr2.b[0]
			<< " to " << rr1.b[0] << endl;
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		// Map from variables occuring in rr1 to frozen symbols
		map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);
		// Map from frozen symbols to variables occuring in rr1
		map<elem, elem> unfreeze_map;
		for(const auto &[k, v] : freeze_map) {
			unfreeze_map[v] = k;
		}

		// Build up the extensional database necessary to check homomorphism.
		set<raw_term> edb;
		// Map from term ids to terms in rr1
		map<elem, raw_term> term_map;
		int j = 0;
		// First put the frozen terms of rr1 into our containment program
		for(raw_term &rt : frozen_rr1.b[0]) {
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
		if(!tables::run_prog_wedb(edb, nrp, d, opts, results)) return false;
		for(const raw_term &res : results) {
			// If the result comes from the containment query (i.e. it is not
			// one of the frozen terms), then there is a homomorphism between
			// the bodies
			raw_term hd_src = rr2.h[0];
			if(res.e[0] == hd_src.e[0]) {
				var_subs var_map;
				set<raw_term> target_terms;
				// Now we want to express the homomorphism in terms of the
				// original (non-frozen) variables and terms of rr1.
				for(size_t i = 2; i < res.e.size() - 1; i++) {
					// If current variable is a body var
					if(rr2_body_vars_set.find(hd_src.e[i]) != rr2_body_vars_set.end()) {
						// Then trace the original var through the unfreeze map
						var_map[hd_src.e[i]] = at_default(unfreeze_map, res.e[i], res.e[i]);
					} else {
						// Otherwise trace the original term through the term map
						target_terms.insert(term_map[res.e[i]]);
					}
				}
				homs.insert(make_pair(target_terms, var_map));
				// Print the homomorphism found
				o::dbg() << "Found homomorphism from " << rr2.b[0] << " to "
					<< target_terms << " under mapping {";
				for(auto &[k, v] : var_map) {
					o::dbg() << k << " -> " << v << ", ";
				}
				o::dbg() << "}" << endl;
			}
		}
		// If no results produced, then there is no homomorphism.
		return true;
	} else {
		return false;
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
	for(raw_rule &rr2 : rp.r) {
		// Because we use a conjunctive homomorphism finding rule
		if(is_cq(rr2) && rr2.b[0].size() > 1) {
			// The variables of the current rule that we'd need to be able to
			// constrain/substitute into
			set<elem> needed_vars;
			set<tuple<raw_rule *, terms_hom>> agg;
			// Now let's look for rules that we can substitute the current
			// into
			for(raw_rule &rr1 : rp.r) {
				set<terms_hom> homs;
				// Find all the homomorphisms between outer and inner rule. This
				// way we can substitute the outer rule into the inner multiple
				// times.
				if(is_cq(rr1) && cbc(rr1, rr2, homs)) {
					for(const terms_hom &hom : homs) {
						auto &[target_terms, var_map] = hom;
						// Record only those homomorphisms where the target is at
						// least as big as the source for there is no point in
						// replacing a group of terms with a rule utilizing a bigger
						// group.
						if(target_terms.size() >= rr2.b[0].size()) {
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

			if(tmp_rel) {
				// Variables are not exactly what is required. So make relation
				// exporting required variables and note argument order.
				target_rel = elem::fresh_temp_sym(d);
				target_args.assign(needed_vars.begin(), needed_vars.end());
				pending_rules.push_back(raw_rule(raw_term(target_rel, target_args), rr2.b[0]));
			} else {
				// The variables exported by current rule are exactly what is
				// needed by all homomorphisms from current body
				target_rel = rr2.h[0].e[0];
				for(size_t i = 2; i < rr2.h[0].e.size() - 1; i++) {
					target_args.push_back(rr2.h[0].e[i]);
				}
			}

			// Now we go through all the homomorphisms and try to apply
			// substitutions to their targets
			for(auto &[rr1, hom] : agg) {
				// If no temporary relation was created, then don't touch the
				// outer rule as its definition is irreducible.
				if(!tmp_rel && rr1 == &rr2) continue;
				auto &[rts, vs] = hom;
				set<raw_term> rr1_set(rr1->b[0].begin(), rr1->b[0].end());
				// If the target rule still includes the homomorphism target,
				// then ... . Note that this may not be the case as the targets
				// of several homomorphisms could overlap.
				if(includes(rr1_set.begin(), rr1_set.end(), rts.begin(),
						rts.end())) {
					// Remove the homomorphism target from the target rule
					auto it = set_difference(rr1_set.begin(), rr1_set.end(),
						rts.begin(), rts.end(), rr1->b[0].begin());
					rr1->b[0].resize(it - rr1->b[0].begin());
					// And place our chosen head with localized arguments.
					vector<elem> subbed_args;
					for(const elem &e : target_args) {
						// If the current parameter of the outer rule is a constant,
						// then just place it in our new term verbatim
						subbed_args.push_back(at_default(vs, e, e));
					}
					rr1->b[0].push_back(raw_term(target_rel, subbed_args));
				}
			}
		}
	}
	// Now add the pending rules. Done here to prevent movement of rules
	// during potential vector resizing.
	for(const raw_rule &rr : pending_rules) {
		rp.r.push_back(rr);
		o::dbg() << "New Factor Created: " << rr << endl;
	}
}

/* Function to iterate through the partitions of the given set. Calls
 * the supplied function with a vector of sets representing each
 * partition. If the supplied function returns false, then the iteration
 * stops. */

template<typename T, typename F> bool partition_iter(set<T> &vars,
		vector<set<T>> &partition, const F &f) {
	if(vars.empty()) {
		return f(partition);
	} else {
		const T nvar = *vars.begin();
		vars.erase(nvar);
		for(size_t i = 0; i < partition.size(); i++) {
			partition[i].insert(nvar);
			if(!partition_iter(vars, partition, f)) {
				return false;
			}
			partition[i].erase(nvar);
		}
		set<T> npart = { nvar };
		partition.push_back(npart);
		if(!partition_iter(vars, partition, f)) {
			return false;
		}
		partition.pop_back();
		vars.insert(nvar);
		return true;
	}
}

/* Function to iterate through the given set raised to the given
 * cartesian power. The supplied function is called with each tuple in
 * the product and if it returns false, the iteration stops. */

template<typename T, typename F>
		bool product_iter(const set<T> &vars, vector<T> &seq,
			size_t len, const F &f) {
	if(len == 0) {
		return f(seq);
	} else {
		for(const T &el : vars) {
			seq.push_back(el);
			if(!product_iter(vars, seq, len - 1, f)) {
				return false;
			}
			seq.pop_back();
		}
		return true;
	}
}

/* Function to iterate through the power set of the given set. The
 * supplied function is called with each element of the power set and
 * if it returns false, the iteration stops. */

template<typename T, typename F> bool power_iter(set<T> &elts,
		set<T> &subset, const F &f) {
	if(elts.size() == 0) {
		return f(subset);
	} else {
		const T nelt = *elts.begin();
		elts.erase(nelt);
		// Case where current element will not be in subset
		if(!power_iter(elts, subset, f)) {
			return false;
		}
		if(subset.insert(nelt).second) {
			// Case where current element will be in subset
			if(!power_iter(elts, subset, f)) {
				return false;
			}
			subset.erase(nelt);
		}
		elts.insert(nelt);
		return true;
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
		void collect_vars(InputIterator first, InputIterator last,
			set<elem> &vars) {
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

/* If rr1 and rr2 are both conjunctive queries with negation, check that
 * rr1 is contained by rr2. Do this using the Levy-Sagiv test. */

bool driver::cqnc(const raw_rule &rr1, const raw_rule &rr2) {
	// Check that rules have correct format
	if(!(is_cqn(rr1) && is_cqn(rr2) &&
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
			for(const set<elem> &s : partition) {
				o::dbg() << "{";
				for(const elem &e : s) {
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
			for(const set<elem> &part : partition) {
				elem pvar = elem::fresh_sym(d);
				for(const elem &e : part) {
					subs[e] = pvar;
				}
			}
			raw_rule subbed = freeze_rule(rr1, subs, d);
			set<raw_term> canonical, canonical_negative;
			// Separate the positive and negative subgoals. Note the symbols
			// supplied to the subgoals.
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					rt.neg = false;
					canonical_negative.insert(rt);
					rt.neg = true;
				} else {
					canonical.insert(rt);
				}
			}
			// Print the canonical database
			o::dbg() << "Current canonical Database: ";
			for(const raw_term &rt : canonical) {
				o::dbg() << rt << ", ";
			}
			o::dbg() << endl;
			// Does canonical database make all the subgoals of subbed true?
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					// If the term in the rule is negated, we need to make sure
					// that it is not in the canonical database.
					rt.neg = false;
					if(canonical.find(rt) != canonical.end()) {
						o::dbg() << "Current canonical database causes its source query to be inconsistent."
							<< endl;
						return true;
					}
					rt.neg = true;
				}
			}
			// Collect the symbols/literals from the freeze map
			set<elem> symbol_set;
			for(const auto &[elm, sym] : subs) {
				symbol_set.insert(sym);
				// Finer control over elements in the universe is required to
				// make this algorithm work with unsafe negations. In
				// particular, we need need to control over which characters and
				// numbers are in the domain.
				if(sym.type == elem::SYM) {
					d.get_sym(sym.e);
				}
			}
			// Get all the relations used in both queries
			set<rel_info> rels;
			for(const raw_term &rt : rr1.b[0]) {
				rels.insert(get_relation_info(rt));
			}
			for(const raw_term &rt : rr2.b[0]) {
				rels.insert(get_relation_info(rt));
			}
			// Now we need to get the largest superset of our canonical
			// database
			set<raw_term> superset;
			for(const rel_info &ri : rels) {
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
			for(const raw_term &rt : canonical_negative) {
				superset.erase(rt);
			}
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

	if(contained) {
		o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
		return true;
	} else {
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
		return false;
	}
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
		raw_form_tree &driver::minimize_aux(const raw_rule &ref_rule,
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
			for(auto &[ref_tmp, var_tmp] : bijection
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
			for(auto &[ref_tmp, var_tmp] : bijection
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
			for(auto &[ref_tmp, var_tmp] : bijection
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
void driver::minimize(raw_rule &rr, const F &f) {
	if(rr.is_fact() || rr.is_goal()) return;
	// Switch to the formula tree representation of the rule if this has
	// not yet been done for this is a precondition to minimize_aux. Note
	// the current form so that we can attempt to restore it afterwards.
	bool orig_form = rr.is_dnf();
	rr = rr.try_as_prft();
	// Copy the rule to provide scratch for minimize_aux
	raw_rule var_rule = rr;
	// Now minimize the formula tree of the given rule using the given
	// containment testing function
	minimize_aux(rr, var_rule, *rr.prft, *var_rule.prft, f);
	// If the input rule was in DNF, provide the output in DNF
	if(orig_form) rr = rr.try_as_b();
}

/* Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. */

template<typename F>
void driver::subsume_queries(raw_prog &rp, const F &f) {
	vector<raw_rule> reduced_rules;
	for(raw_rule &rr : rp.r) {
		bool subsumed = false;

		for(auto nrr = reduced_rules.begin(); nrr != reduced_rules.end();) {
			if(f(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				subsumed = true;
				break;
			} else if(f(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				nrr = reduced_rules.erase(nrr);
			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if(!subsumed) {
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

/* Update the number and characters counters as well as the distinct
 * symbol set to account for the given term. */

void update_element_counts(const raw_term &rt, set<elem> &distinct_syms,
		int_t &char_count, int_t &max_int) {
	for(const elem &el : rt.e)
		if(el.type == elem::NUM) max_int = max(max_int, el.num);
		else if(el.type == elem::SYM) distinct_syms.insert(el);
		else if(el.type == elem::CHR) char_count = 256;
}

/* Compute the number of bits required to represent first the largest
 * integer in the given program and second the universe. */

pair<int_t, int_t> prog_bit_len(const raw_prog &rp) {
	int_t max_int = 0, char_count = 0;
	set<elem> distinct_syms;

	for(const raw_rule &rr : rp.r) {
		// Updates the counters based on the heads of the current rule
		for(const raw_term &rt : rr.h)
			update_element_counts(rt, distinct_syms, char_count, max_int);
		// If this is a rule, update the counters based on the body
		if(rr.is_dnf() || rr.is_form()) {
			raw_form_tree prft = *rr.get_prft();
			prefold_tree(prft, monostate {},
				[&](const raw_form_tree &t, monostate) -> monostate {
					if(t.type == elem::NONE)
						update_element_counts(*t.rt, distinct_syms, char_count, max_int);
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

#ifdef WITH_Z3

/* Check query containment for rules of the given program using theorem prover Z3
  and remove subsumed rules. */

void driver::qc_z3 (raw_prog &raw_p) {
	const auto &[int_bit_len, universe_bit_len] = prog_bit_len(raw_p);
	z3_context ctx(int_bit_len, universe_bit_len);
	// Sort rules by relation name and then by tml arity
	auto sort_rp = [](const raw_rule& r1, const raw_rule& r2) {
		if(r1.h[0].e[0] == r2.h[0].e[0])
			return r1.h[0].arity < r2.h[0].arity;
		else return r1.h[0].e[0] < r2.h[0].e[0];
	};
	sort(raw_p.r.begin(), raw_p.r.end(), sort_rp);
	// Lambda for checking comparability of rules
	auto same_cat = [](const raw_rule& r1, const raw_rule& r2) {
	return r1.h[0].e[0] == r2.h[0].e[0] &&
		r1.h[0].arity == r2.h[0].arity;
	};
	// Check query containment in comparable rules
	for (auto selected = raw_p.r.begin(); selected != raw_p.r.end();) {
		for (auto compared = selected + 1; compared != raw_p.r.end();) {
			// Advance selected iterator such that rules are comparable
			bool isEndReached = false;
			while(!isEndReached &&
					!same_cat(*selected, *compared)) {
				selected = compared;
				compared = selected + 1;
				isEndReached = compared == raw_p.r.end();
			} if (isEndReached) break;
			// Check rules for containment
			if (check_qc_z3(*selected, *compared, ctx)) {
				selected = raw_p.r.erase(selected);
				continue;
			} else if(check_qc_z3(*compared, *selected, ctx))
				compared = raw_p.r.erase(compared);
			else ++compared;
		}
		++selected;
	}
}

/* Initialize an empty context that can then be populated with TML to Z3
 * conversions. value_sort is either a bit-vector whose width can
 * contain the enire program universe and will be used for all Z3
 * relation arguments and bool_sort is the "return" type of all
 * relations. */

z3_context::z3_context(size_t arith_bit_len, size_t universe_bit_len) :
		arith_bit_len(arith_bit_len), universe_bit_len(universe_bit_len),
		solver(context), head_rename(context), bool_sort(context.bool_sort()),
		value_sort(context.bv_sort(universe_bit_len ? universe_bit_len : 1)) {
	// Initialize Z3 solver instance parameters
	z3::params p(context);
	p.set(":timeout", 500u);
	// Enable model based quantifier instantiation since we use quantifiers
	p.set("mbqi", true);
	solver.set(p);
}

/* Function to lookup and create where necessary a Z3 representation of
 * a relation. */

z3::func_decl z3_context::rel_to_z3(const raw_term& rt) {
	const auto &rel = rt.e[0];
	const rel_info &rel_sig = get_relation_info(rt);
	if(auto decl = rel_to_decl.find(rel_sig); decl != rel_to_decl.end())
		return decl->second;
	else {
		z3::sort_vector domain(context);
		for (int_t i = rt.get_formal_arity(); i != 0; --i)
			domain.push_back(value_sort);
		z3::func_decl ndecl =
			context.function(rel.to_str().c_str(), domain, bool_sort);
		rel_to_decl.emplace(make_pair(rel_sig, ndecl));
		return ndecl;
	}
}

/* Function to create Z3 representation of global head variable names.
 * The nth head variable is always assigned the same Z3 constant in
 * order to ensure that different rules are comparable. */

z3::expr z3_context::globalHead_to_z3(const int_t pos) {
	for (int_t i=head_rename.size(); i<=pos; ++i)
		head_rename.push_back(z3::expr(context, fresh_constant()));
	return head_rename[pos];
}

/* Function to lookup and create where necessary a Z3 representation of
 * elements. */

z3::expr z3_context::arg_to_z3(const elem& el) {
	if(auto decl = var_to_decl.find(el); decl != var_to_decl.end())
		return decl->second;
	else if(el.type == elem::NUM) {
		const z3::expr &ndecl =
			context.bv_val(el.num, value_sort.bv_size());
		var_to_decl.emplace(make_pair(el, ndecl));
		return ndecl;
	} else {
		const z3::expr &ndecl =
			context.constant(el.to_str().c_str(), value_sort);
		var_to_decl.emplace(make_pair(el, ndecl));
		return ndecl;
	}
}

/* Construct a formula that constrains the head variables. The
 * constraints are of two sorts: the first equate pairwise identical
 * head variables to each other, and the second equate literals to their
 * unique Z3 equivalent. Also exports a mapping of each head element to
 * the Z3 head variable it has been assigned to. */

z3::expr z3_context::z3_head_constraints(const raw_term &head,
		map<elem, z3::expr> &body_rename) {
	z3::expr restr = context.bool_val(true);
	for (size_t i = 0; i < head.e.size() - 3; ++i) {
		const elem &el = head.e[i + 2];
		const z3::expr &var = globalHead_to_z3(i);
		if(const auto &[it, found] = body_rename.try_emplace(el, var); !found)
			restr = restr && it->second == var;
		else if (el.type != elem::VAR)
			restr = restr && var == arg_to_z3(el);
	}
	return restr;
}

/* Given a term, output the equivalent Z3 expression using and updating
 * the mappings in the context as necessary. */

z3::expr z3_context::term_to_z3(const raw_term &rel) {
	if(rel.extype == raw_term::REL) {
		z3::expr_vector vars_of_rel (context);
		for (auto el = rel.e.begin()+2; el != rel.e.end()-1; ++el) {
			// Pushing head variables
			vars_of_rel.push_back(arg_to_z3(*el));
		}
		return rel_to_z3(rel)(vars_of_rel);
	} else if(rel.extype == raw_term::EQ) {
		return arg_to_z3(rel.e[0]) == arg_to_z3(rel.e[2]);
	} else if(rel.extype <= raw_term::LEQ) {
		return arg_to_z3(rel.e[0]) <= arg_to_z3(rel.e[2]);
	} else if(rel.extype <= raw_term::ARITH && rel.e.size() == 5) {
		// Obtain the Z3 equivalents of TML elements
		z3::expr arg1 = arg_to_z3(rel.e[0]), arg2 = arg_to_z3(rel.e[2]),
			arg3 = arg_to_z3(rel.e[4]);
		// The arithmetic universe may be smaller than the entire universe,
		// so zero the high bits of arithmetic expressions to ensure that
		// only the lower bits are relevant in comparisons
		z3::expr embedding = universe_bit_len == arith_bit_len ?
			context.bool_val(true) :
			arg1.extract(universe_bit_len-1, arith_bit_len) == 0 &&
			arg2.extract(universe_bit_len-1, arith_bit_len) == 0 &&
			arg3.extract(universe_bit_len-1, arith_bit_len) == 0;
		// Its possible that the largest integer in TML program is 0. Z3
		// does not support 0-length bit-vectors, so short-circuit
		if(arith_bit_len == 0) return embedding;
		z3::expr arg1_lo = arg1.extract(arith_bit_len-1, 0),
			arg2_lo = arg2.extract(arith_bit_len-1, 0),
			arg3_lo = arg3.extract(arith_bit_len-1, 0);
		// Finally produce the arithmetic constraint based on the low bits
		// of the operands
		switch(rel.arith_op) {
			case ADD: return (arg1_lo + arg2_lo) == arg3_lo && embedding;
			case SUB: return (arg1_lo - arg2_lo) == arg3_lo && embedding;
			case MULT: return (arg1_lo * arg2_lo) == arg3_lo && embedding;
			case SHL: return shl(arg1_lo, arg2_lo) == arg3_lo && embedding;
			case SHR: return lshr(arg1_lo, arg2_lo) == arg3_lo && embedding;
			case BITWAND: return (arg1_lo & arg2_lo) == arg3_lo && embedding;
			case BITWXOR: return (arg1_lo ^ arg2_lo) == arg3_lo && embedding;
			case BITWOR: return (arg1_lo | arg2_lo) == arg3_lo && embedding;
			default: assert(false); //should never reach here
		}
	} else if(rel.extype <= raw_term::ARITH && rel.e.size() == 6) {
		// Obtain the Z3 equivalents of TML elements
		z3::expr arg1 = arg_to_z3(rel.e[0]), arg2 = arg_to_z3(rel.e[2]),
			arg3 = arg_to_z3(rel.e[4]), arg4 = arg_to_z3(rel.e[5]);
		// The arithmetic universe may be smaller than the entire universe,
		// so zero the high bits of arithmetic expressions to ensure that
		// only the lower bits are relevant in comparisons
		z3::expr embedding = universe_bit_len == arith_bit_len ?
			context.bool_val(true) :
			arg1.extract(universe_bit_len-1, arith_bit_len) == 0 &&
			arg2.extract(universe_bit_len-1, arith_bit_len) == 0 &&
			arg3.extract(universe_bit_len-1, arith_bit_len) == 0 &&
			arg4.extract(universe_bit_len-1, arith_bit_len) == 0;
		// Its possible that the largest integer in TML program is 0. Z3
		// does not support 0-length bit-vectors, so short-circuit
		if(arith_bit_len == 0) return embedding;
		// Since this is double precision arithmetic, join the 3rd and 4th
		// operands to form the RHS
		z3::expr arg1_lo = zext(arg1.extract(arith_bit_len-1, 0), arith_bit_len),
			arg2_lo = zext(arg2.extract(arith_bit_len-1, 0), arith_bit_len),
			arg34 = concat(arg3.extract(arith_bit_len-1, 0),
				arg4.extract(arith_bit_len-1, 0));
		// Finally produce the arithmetic constraint based on the low bits
		// of the LHS operands and full bits of the RHS operand
		switch(rel.arith_op) {
			case ADD: return embedding && (arg1_lo + arg2_lo) == arg34;
			case MULT: return embedding && (arg1_lo * arg2_lo) == arg34;
			default: assert(false); //should never reach here
		}
	} else assert(false); //should never reach here
}

/* Make a fresh Z3 constant. */

z3::expr z3_context::fresh_constant() {
	return z3::expr(context,
		Z3_mk_fresh_const(context, nullptr, value_sort));
}

/* Given a formula tree, output the equivalent Z3 expression using and
 * updating the mappings in the context as necessary. */

z3::expr z3_context::tree_to_z3(const raw_form_tree &t, dict_t &dict) {
	switch(t.type) {
		case elem::AND:
			return tree_to_z3(*t.l, dict) &&
				tree_to_z3(*t.r, dict);
		case elem::ALT:
			return tree_to_z3(*t.l, dict) ||
				tree_to_z3(*t.r, dict);
		case elem::NOT:
			return !tree_to_z3(*t.l, dict);
		case elem::EXISTS: {
			const elem &qvar = *t.l->el;
			// Obtain original Z3 binding this quantified variable
			z3::expr normal_const = arg_to_z3(qvar);
			// Use a fresh Z3 binding for this quantified variable
			z3::expr &temp_const = var_to_decl.at(qvar) = fresh_constant();
			// Make quantified expression
			z3::expr qexpr = exists(temp_const,
				tree_to_z3(*t.r, dict));
			// Restore original binding for quantified variable
			var_to_decl.at(qvar) = normal_const;
			return qexpr;
		} case elem::FORALL: {
			const elem &qvar = *t.l->el;
			// Obtain original Z3 binding this quantified variable
			z3::expr normal_const = arg_to_z3(qvar);
			// Use a fresh Z3 binding for this quantified variable
			z3::expr &temp_const = var_to_decl.at(qvar) = fresh_constant();
			// Make quantified expression
			z3::expr qexpr = forall(temp_const,
				tree_to_z3(*t.r, dict));
			// Restore original binding for quantified variable
			var_to_decl.at(qvar) = normal_const;
			return qexpr;
		} case elem::IMPLIES: case elem::COIMPLIES: case elem::UNIQUE:
			// Process the expanded formula instead
			return tree_to_z3(expand_formula_node(t, dict), dict);
		case elem::NONE: return term_to_z3(*t.rt);
		default:
			assert(false); //should never reach here
	}
}

/* Given a rule, output the body of this rule converted to the
 * corresponding Z3 expression. Caches the conversion in the context in
 * case the same rule is needed in future. */

z3::expr z3_context::rule_to_z3(const raw_rule &rr, dict_t &dict) {
	if(auto decl = rule_to_decl.find(rr); decl != rule_to_decl.end())
		return decl->second;
	// create map from bound_vars
	map<elem, z3::expr> body_rename;
	z3::expr restr = z3_head_constraints(rr.h[0], body_rename);
	// Collect bound variables of rule and restrictions from constants in head
	set<elem> free_vars;
	vector<elem> bound_vars(rr.h[0].e.begin() + 2, rr.h[0].e.end() - 1);
	collect_free_vars(*rr.get_prft(), bound_vars, free_vars);
	// Free variables are existentially quantified
	z3::expr_vector ex_quant_vars (context);
	for (const auto& var : free_vars)
		ex_quant_vars.push_back(arg_to_z3(var));
	map<elem, z3::expr> var_backup;
	// For the intent of constructing this Z3 expression, replace head
	// variable expressions with the corresponding global head
	for(auto &[el, constant] : body_rename) {
		var_backup.emplace(make_pair(el, arg_to_z3(el)));
		var_to_decl.at(el) = constant;
	}
	// Construct z3 expression from rule
	z3::expr formula = tree_to_z3(*rr.get_prft(), dict);
	// Now undo the global head mapping for future constructions
	for(auto &[el, constant] : var_backup) var_to_decl.at(el) = constant;
	z3::expr decl = restr && (ex_quant_vars.empty() ?
		formula : z3::exists(ex_quant_vars, formula));
	rule_to_decl.emplace(make_pair(rr, decl));
	return decl;
}

/* Checks if r1 is contained in r2 or vice versa.
 * Returns false if rules are not comparable or not contained.
 * Returns true if r1 is contained in r2. */

bool driver::check_qc_z3(const raw_rule &r1, const raw_rule &r2,
		z3_context &ctx) {
	if (!(is_query(r1) && is_query(r2))) return false;
	// Check if rules are comparable
	if (! (r1.h[0].e[0] == r2.h[0].e[0] &&
				r1.h[0].arity == r2.h[0].arity)) return 0;
	o::dbg() << "Z3 QC Testing if " << r1 << " <= " << r2 << " : ";
	// Get head variables for z3
	z3::expr_vector bound_vars(ctx.context);
	for (uint_t i = 0; i != r1.h[0].e.size() - 3; ++i)
		bound_vars.push_back(ctx.globalHead_to_z3(i));
	// Rename head variables on the fly such that they match
	// on both rules
	dict_t &dict = tbl->get_dict();
	z3::expr rule1 = ctx.rule_to_z3(r1, dict);
	z3::expr rule2 = ctx.rule_to_z3(r2, dict);
	ctx.solver.push();
	// Add r1 => r2 to solver
	if (bound_vars.empty()) ctx.solver.add(!z3::implies(rule1, rule2));
	else ctx.solver.add(!z3::forall(bound_vars,z3::implies(rule1, rule2)));
	bool res = ctx.solver.check() == z3::unsat;
	ctx.solver.pop();
	o::dbg() << res << endl;
	return res;
}

#endif

/* Make relations mapping list ID's to their heads and tails. Domain's
 * first argument is the relation into which it should put the domain it
 * creates, its second argument is the domain size of of its tuple
 * elements, and its third argument is the maximum tuple length. */

bool driver::transform_domains(raw_prog &rp, const directive& drt) {
	o::dbg() << "Generating domain for: " << drt << endl;
	dict_t &d = tbl->get_dict();
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
	elem lt_elem(elem::LT, d.get_lexeme("<")),
		leq_elem(elem::LEQ, d.get_lexeme("<=")),
		plus_elem(elem::ARITH, t_arith_op::ADD, d.get_lexeme("+")),
		equals_elem(elem::EQ, d.get_lexeme("=")),
		list_id = elem::fresh_var(d), list_fst = elem::fresh_var(d),
		list_rst = elem::fresh_var(d), pred_id = elem::fresh_var(d),
		divisor_x_quotient = gen_limit == 1 ? list_rst : elem::fresh_var(d);

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
			elem new_quotient_elem = elem::fresh_var(d);
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
				quotient / 2 == 1 ? list_rst : elem::fresh_var(d);
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
	elem current_list = elem::fresh_var(d), next_list = elem::fresh_var(d);
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
		next_list = elem::fresh_var(d);
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
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	elem term_id(part_count++);
	if(head.extype == raw_term::REL) {
		elem elems_id = elem::fresh_var(d), tags_id = elem::fresh_var(d),
			elems_hid = elems_id, tags_hid = tags_id;
		vector<raw_term> params_body, param_types_body;
		for(size_t param_idx = 2; param_idx < head.e.size() - 1; param_idx ++) {
			elem next_elems_id = elem::fresh_var(d),
				next_tags_id = elem::fresh_var(d);
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
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
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
			elem qvar = quote_elem(*(t.l->el), variables, d);
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
			elem qvar = quote_elem(*(t.l->el), variables, d);
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
			elem qvar = quote_elem(*(t.l->el), variables, d);
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
	dict_t &d = tbl->get_dict();
	// Make lexeme from concatenating rel's lexeme with the given suffix
	return elem(elem::SYM,
		d.get_lexeme(lexeme2str(rel.e) + to_string_t(suffix)));
}

/* Returns a lexeme formed by concatenating the given string to the
 * given lexeme. Used for refering to sub relations. */

lexeme driver::concat(const lexeme &rel, string suffix) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// Make lexeme from concatenating rel's lexeme with the given suffix
	return d.get_lexeme(lexeme2str(rel) + to_string_t(suffix));
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
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();

	// Create the symbols and variables that will feature heavily in
	// the terms to be created below
	elem decode_tmp_rel = concat(codec_rel, "__decode"),
		name_var = elem::fresh_var(d), timestep_var = elem::fresh_var(d),
		next_timestep_var = elem::fresh_var(d), params_var = elem::fresh_var(d);

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
		params_vars.push_back(elem::fresh_var(d));
		param_vars.push_back(elem::fresh_var(d));
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

/* Transform the given program into a P-DATALOG program, execute the
 * given transformation, then transform the program back into TML. Part
 * of the effect of the transformation into P-DATALOG is to remove
 * deletion rules and add rules that explicitly carry facts from
 * previous steps. Part of the effect of the transformation from
 * P-DATALOG is to remove facts that TML would otherwise persist. */

void driver::pdatalog_transform(raw_prog &rp,
		const function<void(raw_prog &)> &f) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	// Bypass transformation when there are no rules
	if(rp.r.empty()) {
		f(rp);
		return;
	}

	map<rel_info, array<elem, 2>> freeze_map;
	// First move all additions to a relation to a separate temporary
	// relation and move all deletions to another separate temporary
	// relation. Exclude facts from this exercise.
	for(raw_rule &rr : rp.r) {
		for(raw_term &rt : rr.h) {
			rel_info orig_rel = get_relation_info(rt);
			if(auto it = freeze_map.find(orig_rel); it != freeze_map.end()) {
				rt.e[0] = (rr.is_fact() || rr.is_goal()) ? rt.e[0] : it->second[rt.neg];
			} else {
				// Make separate relations to separately hold the positive and
				// negative derivations
				elem pos_frozen_elem = elem::fresh_temp_sym(d);
				elem neg_frozen_elem = elem::fresh_temp_sym(d);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				freeze_map[orig_rel] = {pos_frozen_elem, neg_frozen_elem};
				rt.e[0] = (rr.is_fact() || rr.is_goal()) ?
					rt.e[0] : freeze_map[orig_rel][rt.neg];
				// Ensure that these positive and negative part relations are
				// hidden from the user
				rp.hidden_rels.insert({ pos_frozen_elem.e, rt.arity });
				rp.hidden_rels.insert({ neg_frozen_elem.e, rt.arity });
			}
			// Ensure that facts are added as opposed to deleted from the
			// negative and positive part relations
			if(!rr.is_fact() && !rr.is_goal()) rt.neg = false;
		}
	}
	// Now make rules to add/delete facts from the final relation as well
	// as persist facts from the previous step. This is to simulate TML
	// using P-DATALOG.
	for(const auto &[orig_rel, frozen_elems] : freeze_map) {
		/* The translation is as follows:
		 * hello(?x) :- A.
		 * ~hello(?x) :- B.
		 * TO
		 * ins_hello(?x) :- A.
		 * prev_hello(?x) :- hello(?x).
		 * del_hello(?x) :- B.
		 * hello(?x) :- ins_hello(?x), ~del_hello(?x).
		 * hello(?x) :- prev_hello(?x), ~del_hello(?x).
		 * contradiction() :- ins_hello(?x), del_hello(?x). */
		raw_term original_head = relation_to_term(orig_rel), ins_head, del_head, prev_head;
		ins_head = del_head = prev_head = original_head;
		ins_head.e[0] = frozen_elems[false];
		del_head.e[0] = frozen_elems[true];
		prev_head.e[0] = elem::fresh_temp_sym(d);
		rp.r.push_back(raw_rule(prev_head, original_head));
		rp.r.push_back(raw_rule(original_head, {ins_head, del_head.negate()}));
		rp.r.push_back(raw_rule(original_head, {prev_head, del_head.negate()}));
		rp.hidden_rels.insert({ prev_head.e[0].e, original_head.arity });
	}
	// Run the supplied transformation
	f(rp);
	const raw_term tick(elem::fresh_temp_sym(d), vector<elem> {});
	map<rel_info, elem> scratch_map;
	// Map the program rules to temporary relations and execute them only
	// when the clock is in low state. A temporary relation is required to
	// give us time to delete facts not derived in this step.
	for(raw_rule &rr : rp.r) {
		if(!rr.is_fact() && !rr.is_goal()) {
			for(raw_term &rt : rr.h) {
				rel_info orig_rel = get_relation_info(rt);
				if(auto it = scratch_map.find(orig_rel); it != scratch_map.end()) {
					rt.e[0] = it->second;
				} else {
					elem frozen_elem = elem::fresh_temp_sym(d);
					// Store the mapping so that everything from this relation is
					// moved to a single designated relation.
					rt.e[0] = scratch_map[orig_rel] = frozen_elem;
					rp.hidden_rels.insert({ frozen_elem.e, rt.arity });
				}
			}
			// Condition the rule to execute only on low states.
			rr.set_prft(raw_form_tree(elem::AND,
				make_shared<raw_form_tree>(*rr.get_prft()),
				make_shared<raw_form_tree>(tick.negate())));
		}
	}
	// Now make the rules simulating P-DATALOG in TML. This is essentially
	// done by clearing the temporary relation after each step and doing
	// the necessary additions/deletions to make the final relation
	// reflect this.
	for(const auto &[orig_rel, scratch] : scratch_map) {
		/* The translation is as follows:
		 * hello(?x) :- A.
		 * TO
		 * hello_tmp(?x) :- A, ~tick().
		 * hello(?x) :- hello_tmp(?x), tick().
		 * ~hello(?x) :- ~hello_tmp(?x), tick().
		 * ~hello_tmp(?x) :- tick().
		 * tick() :- ~tick().
		 * ~tick() :- tick(). */
		raw_term original_head = relation_to_term(orig_rel), scratch_head;
		scratch_head = original_head;
		scratch_head.e[0] = scratch;
		rp.r.push_back(raw_rule(original_head, { scratch_head, tick }));
		rp.r.push_back(raw_rule(original_head.negate(), { scratch_head.negate(), tick }));
		rp.r.push_back(raw_rule(scratch_head.negate(), tick ));
	}
	// Make the clock alternate between two states
	rp.r.push_back(raw_rule(tick, tick.negate()));
	rp.r.push_back(raw_rule(tick.negate(), tick));
	rp.hidden_rels.insert({ tick.e[0].e, {0} });
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
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	vector<elem> els = { get<0>(ri), elem_openp };
	for(int_t i = 0; i < get<1>(ri); i++) {
		els.push_back(elem::fresh_var(d));
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
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

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
				elem frozen_elem = elem::fresh_temp_sym(d);
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
		vector<elem> clock_states = { elem::fresh_temp_sym(d) };
		// Push the internal rules onto the program using conditioning to
		// control execution order
		for(const set<const relation *>& v : sorted) {
			// Make a new clock state for the current stage
			const elem clock_state = elem::fresh_temp_sym(d);
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
		raw_term stage0(elem::fresh_temp_sym(d), vector<elem>{});
		raw_term stage1(elem::fresh_temp_sym(d), vector<elem>{});
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

/* Make the given program execute half as fast, that is, two steps of
 * the output program will be equivalent to one step of the original.
 * Useful for debugging the squaring transformation since this is its
 * inverse. */

void driver::square_root_program(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();

	// Only apply this transformation if there are rules to slow down
	if(!rp.r.empty()) {
		// Execute program rules only when the clock is in asserted state
		const raw_term tick(elem::fresh_temp_sym(d), std::vector<elem> {});
		for(raw_rule &rr : rp.r) {
			if(!rr.is_fact() && !rr.is_goal()) {
				rr.set_prft(raw_form_tree(elem::AND,
					make_shared<raw_form_tree>(*rr.get_prft()),
					make_shared<raw_form_tree>(tick)));
			}
		}
		// Make the clock alternate between two states
		rp.r.push_back(raw_rule(tick, tick.negate()));
		rp.r.push_back(raw_rule(tick.negate(), tick));
	}
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
				*rr.prft = raw_form_tree(elem::AND, make_shared<raw_form_tree>(*pprft), prft);
			}
		}
	}
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

/* Eliminate unused elements of hidden relations. Do this by identifying those
 * relation elements that neither participate in term conjunction nor are
 * exported to visible relation nor are used in a negative body term. */

void driver::eliminate_dead_variables(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// Before we can eliminate relation positions, we need to know what
	// rules depend on each relation. Knowing the dependants will allow us
	// to determine whether a certain position is significant, and if so
	// correct the call-sites to match the declaration.
	set<signature> pending_signatures;
	map<signature, set<raw_rule *>> dependants;
	for(raw_rule &rr : rp.r) {
		record_hidden_relation(rp, rr, rr.h[0], pending_signatures, dependants);
		if(!rr.b.empty()) for(const raw_term &rt : rr.b[0])
			record_hidden_relation(rp, rr, rt, pending_signatures, dependants);
	}
	// While there are still signatures to check for reducibility, grab
	// the entire set and try to reduce each relation making a note of
	// affected relations when successful.
	while(!pending_signatures.empty()) {
		// Grab pending signatures
		set<pair<lexeme, ints>> current_signatures = move(pending_signatures);
		for(const signature &sig : current_signatures) {
			// Calculate variable usages so we can know what to eliminate
			ints uses = calculate_variable_usage(sig, dependants);

			// Move forward only if there is something to contract
			if(find(uses.begin(), uses.end(), 1) != uses.end()) {
				// Print active variable usages for debugging purposes
				o::dbg() << "Contracting " << sig.first << " using [";
				const char *sep = "";
				for(int_t count : uses) {
					o::dbg() << sep << count;
					sep = ", ";
				}
				o::dbg() << "]" << endl;

				// Now consistently eliminate certain positions and prepare the
				// next round. Rename the relation after the eliminations in
				// case the new signature coincides with an already existing
				// one.
				elem new_rel = elem::fresh_temp_sym(d);
				for(raw_rule *rr : dependants.at(sig)) {
					contract_term(rr->h[0], new_rel, uses, sig, pending_signatures, rp);
					if(!rr->b.empty()) for(raw_term &rt : rr->b[0])
						contract_term(rt, new_rel, uses, sig, pending_signatures, rp);
				}
				// New signature consists of every variable used more than once
				signature new_sig(new_rel.e,
					{(int_t) count_if(uses.begin(), uses.end(), [](int_t x) { return x > 1; })});
				// Update the dependencies
				dependants[new_sig] = move(dependants.at(sig));
				dependants.erase(sig);
				rp.hidden_rels.insert(new_sig);
			}
		}
	}
	o::dbg() << endl;
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

	//TODO: this is sort of cache to not optimize same program twice
	// but this situation might become evident earlier, i.e if same file is
	// passed as input twice.
	static set<raw_prog *> transformed_progs;
	if(transformed_progs.find(&rp) != transformed_progs.end()) return true;
	transformed_progs.insert(&rp);

	// If we want proof trees, then we need to transform the productions into
	// rules first since only rules are supported by proof trees.
	//if(opts.get_string("proof") != "none") {
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

#ifdef WITH_Z3
		const auto &[int_bit_len, universe_bit_len] = prog_bit_len(rp);
		z3_context z3_ctx(int_bit_len, universe_bit_len);

		if(opts.enabled("qc-subsume-z3")){
			// Trimmed existentials are a precondition to program optimizations
			o::dbg() << "Removing Redundant Quantifiers ..." << endl << endl;
			export_outer_quantifiers(rp);
			o::dbg() << "Query containment subsumption using z3" << endl;
			split_heads(rp);
			subsume_queries(rp,
				[&](const raw_rule &rr1, const raw_rule &rr2)
					{return check_qc_z3(rr1, rr2, z3_ctx);});
			o::dbg() << "Reduced program: " << endl << endl << rp << endl;
		}
#endif

	if(int_t iter_num = opts.get_int("iterate")) {
		// Trimmed existentials are a precondition to program optimizations
		o::dbg() << "Removing Redundant Quantifiers ..." << endl << endl;
		export_outer_quantifiers(rp);

		pdatalog_transform(rp, [&](raw_prog &rp) {
			o::dbg() << "P-DATALOG Pre-Transformation:" << endl << endl << rp << endl;
			split_heads(rp);
			// Alternately square and simplify the program iter_num times
			for(int_t i = 0; i < iter_num; i++) {
				o::dbg() << "Squaring Program ..." << endl << endl;
				square_program(rp);
				o::dbg() << "Squared Program: " << endl << endl << rp << endl;
#ifdef WITH_Z3
				if(opts.enabled("qc-subsume-z3")){
					o::dbg() << "Query containment subsumption using z3" << endl;
					export_outer_quantifiers(rp);
					subsume_queries(rp,
						[&](const raw_rule &rr1, const raw_rule &rr2)
							{return check_qc_z3(rr1, rr2, z3_ctx);});
					o::dbg() << "Reduced program: " << endl << endl << rp << endl;
				}
#endif
				}
			o::dbg() << "P-DATALOG Post-Transformation:" << endl << endl << rp << endl;
		});
	}

/*	if(opts.enabled("cqnc-subsume") || opts.enabled("cqc-subsume") ||
			opts.enabled("cqc-factor") || opts.enabled("split-rules") ||
			opts.enabled("to-dnf")) {
		// Trimmed existentials are a precondition to program optimizations
		o::dbg() << "Removing Redundant Quantifiers ..." << endl << endl;
		export_outer_quantifiers(rp);
		o::dbg() << "Reduced Program:" << endl << endl << rp << endl;

		step_transform(rp, [&](raw_prog &rp) {
			// This transformation is a prerequisite to the CQC and binary
			// transformations, hence its more general activation condition.
			o::dbg() << "Converting to DNF format ..." << endl << endl;
			to_dnf(rp);
			split_heads(rp);
			o::dbg() << "DNF Program:" << endl << endl << rp << endl;

			if(opts.enabled("cqnc-subsume")) {
				o::dbg() << "Subsuming using CQNC test ..." << endl << endl;
				subsume_queries(rp,
					[this](const raw_rule &rr1, const raw_rule &rr2)
						{return cqnc(rr1, rr2);});
				o::dbg() << "CQNC Subsumed Program:" << endl << rp << endl;
			}
			if(opts.enabled("cqc-subsume")) {
				o::dbg() << "Subsuming using CQC test ..." << endl << endl;
				subsume_queries(rp,
					[this](const raw_rule &rr1, const raw_rule &rr2)
						{return cqc(rr1, rr2);});
				o::dbg() << "CQC Subsumed Program:" << endl << rp << endl;
			}
			if(opts.enabled("cqc-factor")) {
				o::dbg() << "Factoring queries using CQC test ..." << endl;
				factor_rules(rp);
				o::dbg() << "Factorized Program:" << endl << rp	<< endl;
			}
			if(opts.enabled("split-rules")) {
				// Though this is a binary transformation, rules will become
				// ternary after timing guards are added
				o::dbg() << "Converting rules to unary form ..." << endl;
				transform_bin(rp);
				o::dbg() << "Binary Program:" << endl << rp << endl;
			}
		});
	}*/

	if(int_t iter_num = opts.get_int("O3")) {
		// Trimmed existentials are a precondition to program optimizations
		o::dbg() << "Removing Redundant Quantifiers ..." << endl << endl;
		export_outer_quantifiers(rp);

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
	}

	if(opts.enabled("O1") || opts.enabled("O2")) {
		mutated_prog mp(rp);
		best_solution bndr(exp_in_heads, mp); 
		optimization_plan plan(bndr);
		// Trimmed existentials are a precondition to program optimizations
		o::dbg() << "Adding export outer quantifiers brancher ..." << endl << endl;
		plan.begin.push_back(bind(&driver::brancher_export_outer_quantifiers, this, placeholders::_1));
		// export_outer_quantifiers(rp);

		step_transform(rp, [&](raw_prog &rp) {
			// This transformation is a prerequisite to the CQC and binary
			// transformations, hence its more general activation condition.
			o::dbg() << "Adding dnf brancher in begin..." << endl << endl;
			plan.begin.push_back(bind(&driver::brancher_to_dnf, this, placeholders::_1));
			o::dbg() << "Adding split heads brancher in begin..." << endl << endl;
			plan.begin.push_back(bind(&driver::brancher_split_heads, this, placeholders::_1));
			// Though this is a binary transformation, rules will become
			// ternary after timing guards are added
			o::dbg() << "Adding split bodies brancher in loop..." << endl << endl;
			plan.loop.push_back(bind(&driver::brancher_split_bodies, this, placeholders::_1));
			o::dbg() << "Adding split heads brancher in loop..." << endl << endl;
			plan.loop.push_back(bind(&driver::brancher_split_heads, this, placeholders::_1));
			if(opts.enabled("O2")) {
				#ifndef WITH_Z3
				o::dbg() << "Adding CQNC brancher ..." << endl << endl;
				plan.loop.push_back(bind(&driver::brancher_subsume_queries_cqnc, this, placeholders::_1));
				o::dbg() << "Adding CQC brancher ..." << endl << endl;
				plan.loop.push_back(bind(&driver::brancher_subsume_queries_cqc, this, placeholders::_1));
				#else
				o::dbg() << "Adding Z3 brancher ..." << endl << endl;
				plan.loop.push_back(bind(&driver::brancher_subsume_queries_z3, this, placeholders::_1));
				#endif
			}
			o::dbg() << "Step Transformed Program:" << endl << rp << endl;
	//		plan.end.push_back(bind(&driver::brancher_eliminate_dead_variables, this, placeholders::_1));
			auto best = optimize(rp, plan);
			rp.r = best.r;
			rp.hidden_rels = best.hidden_rels;
			// rp.r.insert(rp.r.end(), best.r.begin(), best.r.end());
			// rp.r = best.r;
			o::dbg() << "Current:" << endl << rp << endl;

		});
	}

	return true;
}

bool driver::transform_handler(raw_prog &p) {

	// Split heads are a prerequisite to safety checking
	split_heads(p);

#ifdef TYPE_RESOLUTION
	raw_prog tr = ir->generate_type_resolutor(p.nps[0]);
	o::to("transformed") << "Type resolutor Nto1 mapping:\n" << tr << endl;
	rt_options to;
	to.fp_step = opts.enabled("fp");  //disables "__fp__()."
	to.optimize  = false;
	to.bitunv = false;
	to.bproof = proof_mode::none;
	to.show_hidden = false;
	ir_builder ir_handler(dict, to);
	tables tbl_int(dict, to, &ir_handler);
	ir_handler.dynenv = &tbl_int;
	ir_handler.printer = &tbl_int;
	ir_handler.dynenv->bits = 2;
	if (!tbl_int.run_prog(tr, {})) return false;
	DBG(tbl_int.out_fixpoint(o::dump()););
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
	if (opts.enabled("bitunv")) {
		ir->bit_transform(p.nps[0], opts.get_int("bitorder"));
	}
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

	//Work in progress
	if (opts.enabled("guards"))
		// guards transform, will lead to !root_empty
		result = tbl->run_prog(rp.p, pd.strs, steps, break_on_step);
	else
		result = tbl->run_prog((rp.p.nps)[0], pd.strs, steps, break_on_step);

	o::ms() << "# elapsed: ", measure_time_end();

	if (tbl->error) error = true;
	pd.elapsed_steps = nsteps() - step;
	return result;
}

// ----------------------------------------------------------------------------

bool driver::add(input* in) {
	//TODO: handle earlier errors on the input arguments
	if (opts.enabled("earley")) {
		earley_parse_tml(in, rp);
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

driver::driver(string s, const options &o) : opts(o), rp(raw_progs(dict)) {

	if (o.error) { error = true; return; }
	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());
	if (!ii) return;
	if (s.size()) opts.parse(strings{ "-ie", s });
	rt_options to;

	if(auto proof_opt = opts.get("proof"))
		to.bproof = proof_opt->get_enum(map<string, enum proof_mode>
			{{"none", proof_mode::none}, {"tree", proof_mode::tree},
				{"forest", proof_mode::forest}, {"partial-tree", proof_mode::partial_tree},
				{"partial-forest", proof_mode::partial_forest}});
	to.optimize          = opts.enabled("optimize");
	to.print_transformed = opts.enabled("t");
	to.apply_regexpmatch = opts.enabled("regex");
	to.fp_step           = opts.enabled("fp");
	to.show_hidden       = opts.enabled("show-hidden");
	to.bin_lr            = opts.enabled("bin-lr");
	to.bitunv            = opts.enabled("bitunv");
	to.bitorder          = opts.get_int("bitorder");

	//dict belongs to driver and is referenced by ir_builder and tables
	ir = new ir_builder(dict, to);
	tbl = new tables(dict, to, ir);
	ir->dynenv  = tbl;
	ir->printer = tbl; //by now leaving printer component in tables, to be rafactored

	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	tbl->add_print_updates_states(opts.pu_states);
	set_populate_tml_update(opts.enabled("tml_update"));
	set_regex_level(opts.get_int("regex-level"));

	read_inputs();
	if(!error) {
		//FIXME: root_isempty
		directives_load((rp.p.nps)[0]);
		transform_handler(rp.p);
		//TODO: review how recursion to nested programs should be handled
		// per transform vs globally
		//recursive_transform(rp-p);
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
