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
#include "driver.h"
#include "err.h"
#include "archive.h"

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

size_t driver::load_stdin() {
	ostringstream_t ss; ss << CIN.rdbuf();
	pd.std_input = to_string_t(ws2s(ss.str()));
	return pd.std_input.size();
}

void unquote(string_t& str);

string_t driver::directive_load(const directive& d) {
	string_t str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	switch (d.type) {
		case directive::FNAME:
			return to_string_t(input::file_read(to_string(str)));
		case directive::STDIN: return move(pd.std_input);
		default: return unquote(str), str;
	}
	DBGFAIL;
}

signature get_signature(const raw_term &rt) {
	return {rt.e[0].e, rt.arity};
}

void driver::directives_load(raw_prog& p, lexeme& trel) {
//	int_t rel;
	// The list of directives that have been processed so far
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
		case directive::EVAL: transform_evals(p, d); break;
		case directive::QUOTE: transform_quotes(p, d); break;
		case directive::CODEC: transform_codecs(p, d); break;
		case directive::INTERNAL:
			p.hidden_rels.insert(get_signature(d.internal_term)); break;
		case directive::CMDLINE:
			if (d.n < opts.argc())
				pd.strs.emplace(d.rel.e,
					to_string_t(opts.argv(d.n)));
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

optional<pair<elem, raw_rule>> driver::is_safe(raw_prog rp) {
	// Ignore the outermost existential quantifiers
	export_outer_quantifiers(rp);
	// Split heads are a prerequisite to safety checking
	split_heads(rp);
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

/* Convenience function for getting relation name and arity from
 * term. */

rel_info get_relation_info(const raw_term &rt) {
	return make_tuple(rt.e[0], rt.e.size() - 3);
}

/* If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. */

bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	dict_t d;
	d.op = old_dict.op;
	d.cl = old_dict.cl;
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
		raw_prog nrp;
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
	dict_t &old_dict = tbl->get_dict();
	dict_t d;
	d.op = old_dict.op;
	d.cl = old_dict.cl;

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
		raw_prog nrp;
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

	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();

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
			d.op = old_dict.op;
			d.cl = old_dict.cl;

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
					raw_prog test_prog;
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

raw_prog driver::read_prog(elem prog, const raw_prog &rp) {
	lexeme prog_str = {prog.e[0]+1, prog.e[1]-1};
	input *prog_in = dynii.add_string(lexeme2str(prog_str));
	prog_in->prog_lex();
	raw_prog nrp;
	nrp.builtins = rp.builtins;
	nrp.parse(prog_in, tbl->get_dict());
	const strs_t strs;
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
		raw_prog nrp = read_prog(quote_str, rp);
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

/* If eval is used, take its four arguments: the name of the relation
 * that will contain the outputs of the original TML program, the formal
 * name of the relation containing the quoted program's domain, the
 * formal name of the relation containing a representation of a TML
 * program, and the number of steps of the quoted program that should be
 * simulated. Note that the evaled relation will only depend on the
 * relation's program arity and its name - not its entries. Note also
 * that the bulk of this function is autogenerated by calling this
 * interepreter on eval.tml using the flag --program_gen (which in turn
 * is implemented by the generate_cpp function). */

bool driver::transform_evals(raw_prog &rp, const directive &drt) {
	if(drt.type != directive::EVAL) return false;
	o::dbg() << "Generating eval for: " << drt << endl;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem out_rel = drt.eval_sym;
	// The relation containing the quotation arity is the second symbol
	// between the parentheses
	elem domain_sym = drt.domain_sym;
	// The formal symbol representing the quotation relation is the
	// third symbol between the parentheses
	elem quote_sym = drt.quote_sym;
	// The number representing how many database steps to interpret is
	// the fourth symbol between the parentheses
	int_t timeout = drt.timeout_num.num;
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();

	{
		directive dir0;
		dir0.type = directive::INTERNAL;
		elem e1(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_tick"));
		elem e2(elem::OPENP, t_arith_op::NOP, d.get_lexeme("("));
		elem e3(elem::CLOSEP, t_arith_op::NOP, d.get_lexeme(")"));
		raw_term rt4(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt4.neg = false;
		dir0.internal_term = rt4;
		directive dir5;
		dir5.type = directive::INTERNAL;
		elem e6(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_tock"));
		raw_term rt7(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt7.neg = false;
		dir5.internal_term = rt7;
		directive dir8;
		dir8.type = directive::INTERNAL;
		elem e9(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e10(elem::VAR, t_arith_op::NOP, d.get_lexeme("?x"));
		raw_term rt11(raw_term::REL, t_arith_op::NOP, {e9, e2, e10, e3, });
		rt11.neg = false;
		dir8.internal_term = rt11;
		directive dir12;
		dir12.type = directive::INTERNAL;
		elem e13(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt14(raw_term::REL, t_arith_op::NOP, {e13, e2, e10, e3, });
		rt14.neg = false;
		dir12.internal_term = rt14;
		directive dir15;
		dir15.type = directive::INTERNAL;
		elem e16(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e17(elem::VAR, t_arith_op::NOP, d.get_lexeme("?in"));
		elem e18(elem::VAR, t_arith_op::NOP, d.get_lexeme("?idx"));
		elem e19(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out"));
		raw_term rt20(raw_term::REL, t_arith_op::NOP, {e16, e2, e17, e18, e19, e3, });
		rt20.neg = false;
		dir15.internal_term = rt20;
		directive dir21;
		dir21.type = directive::INTERNAL;
		elem e22(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e23(elem::VAR, t_arith_op::NOP, d.get_lexeme("?val"));
		raw_term rt24(raw_term::REL, t_arith_op::NOP, {e22, e2, e17, e18, e23, e3, });
		rt24.neg = false;
		dir21.internal_term = rt24;
		directive dir25;
		dir25.type = directive::INTERNAL;
		elem e26(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e27(elem::VAR, t_arith_op::NOP, d.get_lexeme("?lst"));
		elem e28(elem::VAR, t_arith_op::NOP, d.get_lexeme("?inds"));
		elem e29(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals"));
		raw_term rt30(raw_term::REL, t_arith_op::NOP, {e26, e2, e27, e28, e29, e3, });
		rt30.neg = false;
		dir25.internal_term = rt30;
		directive dir31;
		dir31.type = directive::INTERNAL;
		elem e32(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e33(elem::VAR, t_arith_op::NOP, d.get_lexeme("?chks"));
		raw_term rt34(raw_term::REL, t_arith_op::NOP, {e32, e2, e17, e33, e19, e3, });
		rt34.neg = false;
		dir31.internal_term = rt34;
		directive dir35;
		dir35.type = directive::INTERNAL;
		elem e36(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt37(raw_term::REL, t_arith_op::NOP, {e36, e2, e17, e33, e19, e3, });
		rt37.neg = false;
		dir35.internal_term = rt37;
		directive dir38;
		dir38.type = directive::INTERNAL;
		elem e39(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e40(elem::VAR, t_arith_op::NOP, d.get_lexeme("?ts"));
		elem e41(elem::VAR, t_arith_op::NOP, d.get_lexeme("?id"));
		raw_term rt42(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt42.neg = false;
		dir38.internal_term = rt42;
		directive dir43;
		dir43.type = directive::INTERNAL;
		elem e44(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e45(elem::VAR, t_arith_op::NOP, d.get_lexeme("?name"));
		raw_term rt46(raw_term::REL, t_arith_op::NOP, {e44, e2, e40, e45, e19, e3, });
		rt46.neg = false;
		dir43.internal_term = rt46;
		directive dir47;
		dir47.type = directive::INTERNAL;
		elem e48(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt49(raw_term::REL, t_arith_op::NOP, {e48, e2, e40, e45, e19, e3, });
		rt49.neg = false;
		dir47.internal_term = rt49;
		directive dir50;
		dir50.type = directive::INTERNAL;
		elem e51(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e52(elem::VAR, t_arith_op::NOP, d.get_lexeme("?nts"));
		raw_term rt53(raw_term::REL, t_arith_op::NOP, {e51, e2, e52, e45, e19, e3, });
		rt53.neg = false;
		dir50.internal_term = rt53;
		directive dir54;
		dir54.type = directive::INTERNAL;
		elem e55(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt56(raw_term::REL, t_arith_op::NOP, {e55, e2, e40, e52, e3, });
		rt56.neg = false;
		dir54.internal_term = rt56;
		directive dir57;
		dir57.type = directive::INTERNAL;
		elem e58(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt59(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt59.neg = false;
		dir57.internal_term = rt59;
		directive dir60;
		dir60.type = directive::INTERNAL;
		elem e61(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_databases"));
		raw_term rt62(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt62.neg = false;
		dir60.internal_term = rt62;
		directive dir63;
		dir63.type = directive::INTERNAL;
		elem e64(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt65(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e41, e19, e3, });
		rt65.neg = false;
		dir63.internal_term = rt65;
		directive dir66;
		dir66.type = directive::INTERNAL;
		elem e67(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_fixpoint"));
		raw_term rt68(raw_term::REL, t_arith_op::NOP, {e67, e2, e40, e52, e3, });
		rt68.neg = false;
		dir66.internal_term = rt68;
		raw_term rt69(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt69.neg = false;
		raw_term rt73(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt73.neg = false;
		sprawformtree ft72 = std::make_shared<raw_form_tree>(rt73);
		sprawformtree ft71 = std::make_shared<raw_form_tree>(elem::NOT, ft72);
		raw_term rt76(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt76.neg = false;
		sprawformtree ft75 = std::make_shared<raw_form_tree>(rt76);
		sprawformtree ft74 = std::make_shared<raw_form_tree>(elem::NOT, ft75);
		sprawformtree ft70 = std::make_shared<raw_form_tree>(elem::AND, ft71, ft74);
		raw_rule rr77({rt69, }, ft70);
		raw_term rt78(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt78.neg = false;
		raw_term rt79(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt79.neg = true;
		raw_term rt81(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt81.neg = false;
		sprawformtree ft80 = std::make_shared<raw_form_tree>(rt81);
		raw_rule rr82({rt78, rt79, }, ft80);
		raw_term rt83(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt83.neg = false;
		raw_term rt84(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt84.neg = true;
		raw_term rt86(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt86.neg = false;
		sprawformtree ft85 = std::make_shared<raw_form_tree>(rt86);
		raw_rule rr87({rt83, rt84, }, ft85);
		raw_term rt88(raw_term::REL, t_arith_op::NOP, {e9, e2, e10, e3, });
		rt88.neg = false;
		elem e90(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_fst"));
		elem e91(elem::VAR, t_arith_op::NOP, d.get_lexeme("?a"));
		raw_term rt92(raw_term::REL, t_arith_op::NOP, {e90, e2, e91, e10, e3, });
		rt92.neg = false;
		sprawformtree ft89 = std::make_shared<raw_form_tree>(rt92);
		raw_rule rr93({rt88, }, ft89);
		raw_term rt94(raw_term::REL, t_arith_op::NOP, {e13, e2, e10, e3, });
		rt94.neg = false;
		raw_term rt96(raw_term::REL, t_arith_op::NOP, {e90, e2, e10, e91, e3, });
		rt96.neg = false;
		sprawformtree ft95 = std::make_shared<raw_form_tree>(rt96);
		raw_rule rr97({rt94, }, ft95);
		raw_term rt98(raw_term::REL, t_arith_op::NOP, {e13, e2, e10, e3, });
		rt98.neg = false;
		elem e100(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_nil"));
		raw_term rt101(raw_term::REL, t_arith_op::NOP, {e100, e2, e10, e3, });
		rt101.neg = false;
		sprawformtree ft99 = std::make_shared<raw_form_tree>(rt101);
		raw_rule rr102({rt98, }, ft99);
		raw_term rt103(raw_term::REL, t_arith_op::NOP, {e16, e2, e17, e18, e19, e3, });
		rt103.neg = false;
		elem e112(elem::GT, t_arith_op::NOP, d.get_lexeme(">"));
		elem e113(int_t(0));
		raw_term rt114(raw_term::LEQ, t_arith_op::NOP, {e18, e112, e113, });
		rt114.neg = false;
		sprawformtree ft111 = std::make_shared<raw_form_tree>(rt114);
		sprawformtree ft110 = std::make_shared<raw_form_tree>(elem::NOT, ft111);
		elem e116(elem::VAR, t_arith_op::NOP, d.get_lexeme("?pred"));
		elem e117(elem::ARITH, t_arith_op::ADD, d.get_lexeme("+"));
		elem e118(int_t(1));
		elem e119(elem::EQ, t_arith_op::NOP, d.get_lexeme("="));
		raw_term rt120(raw_term::ARITH, t_arith_op::ADD, {e116, e117, e118, e119, e18, });
		rt120.neg = false;
		sprawformtree ft115 = std::make_shared<raw_form_tree>(rt120);
		sprawformtree ft109 = std::make_shared<raw_form_tree>(elem::AND, ft110, ft115);
		elem e122(elem::VAR, t_arith_op::NOP, d.get_lexeme("?in_hd"));
		raw_term rt123(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt123.neg = false;
		sprawformtree ft121 = std::make_shared<raw_form_tree>(rt123);
		sprawformtree ft108 = std::make_shared<raw_form_tree>(elem::AND, ft109, ft121);
		elem e125(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_rst"));
		elem e126(elem::VAR, t_arith_op::NOP, d.get_lexeme("?in_tl"));
		raw_term rt127(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt127.neg = false;
		sprawformtree ft124 = std::make_shared<raw_form_tree>(rt127);
		sprawformtree ft107 = std::make_shared<raw_form_tree>(elem::AND, ft108, ft124);
		elem e129(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out_hd"));
		raw_term rt130(raw_term::REL, t_arith_op::NOP, {e90, e2, e19, e129, e3, });
		rt130.neg = false;
		sprawformtree ft128 = std::make_shared<raw_form_tree>(rt130);
		sprawformtree ft106 = std::make_shared<raw_form_tree>(elem::AND, ft107, ft128);
		elem e132(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out_tl"));
		raw_term rt133(raw_term::REL, t_arith_op::NOP, {e125, e2, e19, e132, e3, });
		rt133.neg = false;
		sprawformtree ft131 = std::make_shared<raw_form_tree>(rt133);
		sprawformtree ft105 = std::make_shared<raw_form_tree>(elem::AND, ft106, ft131);
		raw_term rt135(raw_term::REL, t_arith_op::NOP, {e16, e2, e126, e116, e132, e3, });
		rt135.neg = false;
		sprawformtree ft134 = std::make_shared<raw_form_tree>(rt135);
		sprawformtree ft104 = std::make_shared<raw_form_tree>(elem::AND, ft105, ft134);
		raw_rule rr136({rt103, }, ft104);
		raw_term rt137(raw_term::REL, t_arith_op::NOP, {e16, e2, e17, e113, e19, e3, });
		rt137.neg = false;
		raw_term rt143(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt143.neg = false;
		sprawformtree ft142 = std::make_shared<raw_form_tree>(rt143);
		raw_term rt145(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt145.neg = false;
		sprawformtree ft144 = std::make_shared<raw_form_tree>(rt145);
		sprawformtree ft141 = std::make_shared<raw_form_tree>(elem::AND, ft142, ft144);
		raw_term rt147(raw_term::REL, t_arith_op::NOP, {e9, e2, e129, e3, });
		rt147.neg = false;
		sprawformtree ft146 = std::make_shared<raw_form_tree>(rt147);
		sprawformtree ft140 = std::make_shared<raw_form_tree>(elem::AND, ft141, ft146);
		raw_term rt149(raw_term::REL, t_arith_op::NOP, {e90, e2, e19, e129, e3, });
		rt149.neg = false;
		sprawformtree ft148 = std::make_shared<raw_form_tree>(rt149);
		sprawformtree ft139 = std::make_shared<raw_form_tree>(elem::AND, ft140, ft148);
		raw_term rt151(raw_term::REL, t_arith_op::NOP, {e125, e2, e19, e126, e3, });
		rt151.neg = false;
		sprawformtree ft150 = std::make_shared<raw_form_tree>(rt151);
		sprawformtree ft138 = std::make_shared<raw_form_tree>(elem::AND, ft139, ft150);
		raw_rule rr152({rt137, }, ft138);
		raw_term rt153(raw_term::REL, t_arith_op::NOP, {e22, e2, e17, e18, e23, e3, });
		rt153.neg = false;
		raw_term rt161(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt161.neg = false;
		sprawformtree ft160 = std::make_shared<raw_form_tree>(rt161);
		raw_term rt163(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt163.neg = false;
		sprawformtree ft162 = std::make_shared<raw_form_tree>(rt163);
		sprawformtree ft159 = std::make_shared<raw_form_tree>(elem::AND, ft160, ft162);
		raw_term rt165(raw_term::REL, t_arith_op::NOP, {e22, e2, e126, e116, e23, e3, });
		rt165.neg = false;
		sprawformtree ft164 = std::make_shared<raw_form_tree>(rt165);
		sprawformtree ft158 = std::make_shared<raw_form_tree>(elem::AND, ft159, ft164);
		raw_term rt168(raw_term::LEQ, t_arith_op::NOP, {e18, e112, e113, });
		rt168.neg = false;
		sprawformtree ft167 = std::make_shared<raw_form_tree>(rt168);
		sprawformtree ft166 = std::make_shared<raw_form_tree>(elem::NOT, ft167);
		sprawformtree ft157 = std::make_shared<raw_form_tree>(elem::AND, ft158, ft166);
		raw_term rt170(raw_term::REL, t_arith_op::NOP, {e9, e2, e18, e3, });
		rt170.neg = false;
		sprawformtree ft169 = std::make_shared<raw_form_tree>(rt170);
		sprawformtree ft156 = std::make_shared<raw_form_tree>(elem::AND, ft157, ft169);
		raw_term rt172(raw_term::REL, t_arith_op::NOP, {e9, e2, e23, e3, });
		rt172.neg = false;
		sprawformtree ft171 = std::make_shared<raw_form_tree>(rt172);
		sprawformtree ft155 = std::make_shared<raw_form_tree>(elem::AND, ft156, ft171);
		raw_term rt174(raw_term::ARITH, t_arith_op::ADD, {e116, e117, e118, e119, e18, });
		rt174.neg = false;
		sprawformtree ft173 = std::make_shared<raw_form_tree>(rt174);
		sprawformtree ft154 = std::make_shared<raw_form_tree>(elem::AND, ft155, ft173);
		raw_rule rr175({rt153, }, ft154);
		raw_term rt176(raw_term::REL, t_arith_op::NOP, {e22, e2, e17, e113, e23, e3, });
		rt176.neg = false;
		raw_term rt180(raw_term::REL, t_arith_op::NOP, {e9, e2, e23, e3, });
		rt180.neg = false;
		sprawformtree ft179 = std::make_shared<raw_form_tree>(rt180);
		raw_term rt182(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e23, e3, });
		rt182.neg = false;
		sprawformtree ft181 = std::make_shared<raw_form_tree>(rt182);
		sprawformtree ft178 = std::make_shared<raw_form_tree>(elem::AND, ft179, ft181);
		raw_term rt184(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt184.neg = false;
		sprawformtree ft183 = std::make_shared<raw_form_tree>(rt184);
		sprawformtree ft177 = std::make_shared<raw_form_tree>(elem::AND, ft178, ft183);
		raw_rule rr185({rt176, }, ft177);
		raw_term rt186(raw_term::REL, t_arith_op::NOP, {e26, e2, e27, e28, e29, e3, });
		rt186.neg = false;
		elem e193(elem::VAR, t_arith_op::NOP, d.get_lexeme("?inds_hd"));
		raw_term rt194(raw_term::REL, t_arith_op::NOP, {e90, e2, e28, e193, e3, });
		rt194.neg = false;
		sprawformtree ft192 = std::make_shared<raw_form_tree>(rt194);
		elem e196(elem::VAR, t_arith_op::NOP, d.get_lexeme("?inds_tl"));
		raw_term rt197(raw_term::REL, t_arith_op::NOP, {e125, e2, e28, e196, e3, });
		rt197.neg = false;
		sprawformtree ft195 = std::make_shared<raw_form_tree>(rt197);
		sprawformtree ft191 = std::make_shared<raw_form_tree>(elem::AND, ft192, ft195);
		elem e199(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals_hd"));
		raw_term rt200(raw_term::REL, t_arith_op::NOP, {e90, e2, e29, e199, e3, });
		rt200.neg = false;
		sprawformtree ft198 = std::make_shared<raw_form_tree>(rt200);
		sprawformtree ft190 = std::make_shared<raw_form_tree>(elem::AND, ft191, ft198);
		elem e202(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals_tl"));
		raw_term rt203(raw_term::REL, t_arith_op::NOP, {e125, e2, e29, e202, e3, });
		rt203.neg = false;
		sprawformtree ft201 = std::make_shared<raw_form_tree>(rt203);
		sprawformtree ft189 = std::make_shared<raw_form_tree>(elem::AND, ft190, ft201);
		raw_term rt205(raw_term::REL, t_arith_op::NOP, {e22, e2, e27, e193, e199, e3, });
		rt205.neg = false;
		sprawformtree ft204 = std::make_shared<raw_form_tree>(rt205);
		sprawformtree ft188 = std::make_shared<raw_form_tree>(elem::AND, ft189, ft204);
		raw_term rt207(raw_term::REL, t_arith_op::NOP, {e26, e2, e27, e196, e202, e3, });
		rt207.neg = false;
		sprawformtree ft206 = std::make_shared<raw_form_tree>(rt207);
		sprawformtree ft187 = std::make_shared<raw_form_tree>(elem::AND, ft188, ft206);
		raw_rule rr208({rt186, }, ft187);
		raw_term rt209(raw_term::REL, t_arith_op::NOP, {e26, e2, e27, e28, e29, e3, });
		rt209.neg = false;
		raw_term rt213(raw_term::REL, t_arith_op::NOP, {e13, e2, e27, e3, });
		rt213.neg = false;
		sprawformtree ft212 = std::make_shared<raw_form_tree>(rt213);
		raw_term rt215(raw_term::REL, t_arith_op::NOP, {e100, e2, e28, e3, });
		rt215.neg = false;
		sprawformtree ft214 = std::make_shared<raw_form_tree>(rt215);
		sprawformtree ft211 = std::make_shared<raw_form_tree>(elem::AND, ft212, ft214);
		raw_term rt217(raw_term::REL, t_arith_op::NOP, {e100, e2, e29, e3, });
		rt217.neg = false;
		sprawformtree ft216 = std::make_shared<raw_form_tree>(rt217);
		sprawformtree ft210 = std::make_shared<raw_form_tree>(elem::AND, ft211, ft216);
		raw_rule rr218({rt209, }, ft210);
		raw_term rt219(raw_term::REL, t_arith_op::NOP, {e32, e2, e17, e33, e19, e3, });
		rt219.neg = false;
		raw_term rt227(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt227.neg = false;
		sprawformtree ft226 = std::make_shared<raw_form_tree>(rt227);
		raw_term rt229(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt229.neg = false;
		sprawformtree ft228 = std::make_shared<raw_form_tree>(rt229);
		sprawformtree ft225 = std::make_shared<raw_form_tree>(elem::AND, ft226, ft228);
		raw_term rt231(raw_term::REL, t_arith_op::NOP, {e90, e2, e33, e118, e3, });
		rt231.neg = false;
		sprawformtree ft230 = std::make_shared<raw_form_tree>(rt231);
		sprawformtree ft224 = std::make_shared<raw_form_tree>(elem::AND, ft225, ft230);
		elem e233(elem::VAR, t_arith_op::NOP, d.get_lexeme("?chks_tl"));
		raw_term rt234(raw_term::REL, t_arith_op::NOP, {e125, e2, e33, e233, e3, });
		rt234.neg = false;
		sprawformtree ft232 = std::make_shared<raw_form_tree>(rt234);
		sprawformtree ft223 = std::make_shared<raw_form_tree>(elem::AND, ft224, ft232);
		raw_term rt236(raw_term::REL, t_arith_op::NOP, {e90, e2, e19, e122, e3, });
		rt236.neg = false;
		sprawformtree ft235 = std::make_shared<raw_form_tree>(rt236);
		sprawformtree ft222 = std::make_shared<raw_form_tree>(elem::AND, ft223, ft235);
		raw_term rt238(raw_term::REL, t_arith_op::NOP, {e125, e2, e19, e132, e3, });
		rt238.neg = false;
		sprawformtree ft237 = std::make_shared<raw_form_tree>(rt238);
		sprawformtree ft221 = std::make_shared<raw_form_tree>(elem::AND, ft222, ft237);
		raw_term rt240(raw_term::REL, t_arith_op::NOP, {e32, e2, e126, e233, e132, e3, });
		rt240.neg = false;
		sprawformtree ft239 = std::make_shared<raw_form_tree>(rt240);
		sprawformtree ft220 = std::make_shared<raw_form_tree>(elem::AND, ft221, ft239);
		raw_rule rr241({rt219, }, ft220);
		raw_term rt242(raw_term::REL, t_arith_op::NOP, {e32, e2, e17, e33, e19, e3, });
		rt242.neg = false;
		raw_term rt248(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt248.neg = false;
		sprawformtree ft247 = std::make_shared<raw_form_tree>(rt248);
		raw_term rt250(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt250.neg = false;
		sprawformtree ft249 = std::make_shared<raw_form_tree>(rt250);
		sprawformtree ft246 = std::make_shared<raw_form_tree>(elem::AND, ft247, ft249);
		raw_term rt252(raw_term::REL, t_arith_op::NOP, {e90, e2, e33, e113, e3, });
		rt252.neg = false;
		sprawformtree ft251 = std::make_shared<raw_form_tree>(rt252);
		sprawformtree ft245 = std::make_shared<raw_form_tree>(elem::AND, ft246, ft251);
		raw_term rt254(raw_term::REL, t_arith_op::NOP, {e125, e2, e33, e233, e3, });
		rt254.neg = false;
		sprawformtree ft253 = std::make_shared<raw_form_tree>(rt254);
		sprawformtree ft244 = std::make_shared<raw_form_tree>(elem::AND, ft245, ft253);
		raw_term rt256(raw_term::REL, t_arith_op::NOP, {e32, e2, e126, e233, e19, e3, });
		rt256.neg = false;
		sprawformtree ft255 = std::make_shared<raw_form_tree>(rt256);
		sprawformtree ft243 = std::make_shared<raw_form_tree>(elem::AND, ft244, ft255);
		raw_rule rr257({rt242, }, ft243);
		raw_term rt258(raw_term::REL, t_arith_op::NOP, {e32, e2, e17, e33, e19, e3, });
		rt258.neg = false;
		raw_term rt262(raw_term::REL, t_arith_op::NOP, {e100, e2, e17, e3, });
		rt262.neg = false;
		sprawformtree ft261 = std::make_shared<raw_form_tree>(rt262);
		raw_term rt264(raw_term::REL, t_arith_op::NOP, {e100, e2, e33, e3, });
		rt264.neg = false;
		sprawformtree ft263 = std::make_shared<raw_form_tree>(rt264);
		sprawformtree ft260 = std::make_shared<raw_form_tree>(elem::AND, ft261, ft263);
		raw_term rt266(raw_term::REL, t_arith_op::NOP, {e100, e2, e19, e3, });
		rt266.neg = false;
		sprawformtree ft265 = std::make_shared<raw_form_tree>(rt266);
		sprawformtree ft259 = std::make_shared<raw_form_tree>(elem::AND, ft260, ft265);
		raw_rule rr267({rt258, }, ft259);
		raw_term rt268(raw_term::REL, t_arith_op::NOP, {e36, e2, e17, e33, e19, e3, });
		rt268.neg = false;
		raw_term rt276(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt276.neg = false;
		sprawformtree ft275 = std::make_shared<raw_form_tree>(rt276);
		raw_term rt278(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt278.neg = false;
		sprawformtree ft277 = std::make_shared<raw_form_tree>(rt278);
		sprawformtree ft274 = std::make_shared<raw_form_tree>(elem::AND, ft275, ft277);
		raw_term rt280(raw_term::REL, t_arith_op::NOP, {e90, e2, e33, e113, e3, });
		rt280.neg = false;
		sprawformtree ft279 = std::make_shared<raw_form_tree>(rt280);
		sprawformtree ft273 = std::make_shared<raw_form_tree>(elem::AND, ft274, ft279);
		raw_term rt282(raw_term::REL, t_arith_op::NOP, {e125, e2, e33, e233, e3, });
		rt282.neg = false;
		sprawformtree ft281 = std::make_shared<raw_form_tree>(rt282);
		sprawformtree ft272 = std::make_shared<raw_form_tree>(elem::AND, ft273, ft281);
		raw_term rt284(raw_term::REL, t_arith_op::NOP, {e90, e2, e19, e122, e3, });
		rt284.neg = false;
		sprawformtree ft283 = std::make_shared<raw_form_tree>(rt284);
		sprawformtree ft271 = std::make_shared<raw_form_tree>(elem::AND, ft272, ft283);
		raw_term rt286(raw_term::REL, t_arith_op::NOP, {e125, e2, e19, e132, e3, });
		rt286.neg = false;
		sprawformtree ft285 = std::make_shared<raw_form_tree>(rt286);
		sprawformtree ft270 = std::make_shared<raw_form_tree>(elem::AND, ft271, ft285);
		raw_term rt288(raw_term::REL, t_arith_op::NOP, {e36, e2, e126, e233, e132, e3, });
		rt288.neg = false;
		sprawformtree ft287 = std::make_shared<raw_form_tree>(rt288);
		sprawformtree ft269 = std::make_shared<raw_form_tree>(elem::AND, ft270, ft287);
		raw_rule rr289({rt268, }, ft269);
		raw_term rt290(raw_term::REL, t_arith_op::NOP, {e36, e2, e17, e33, e19, e3, });
		rt290.neg = false;
		raw_term rt296(raw_term::REL, t_arith_op::NOP, {e90, e2, e17, e122, e3, });
		rt296.neg = false;
		sprawformtree ft295 = std::make_shared<raw_form_tree>(rt296);
		raw_term rt298(raw_term::REL, t_arith_op::NOP, {e125, e2, e17, e126, e3, });
		rt298.neg = false;
		sprawformtree ft297 = std::make_shared<raw_form_tree>(rt298);
		sprawformtree ft294 = std::make_shared<raw_form_tree>(elem::AND, ft295, ft297);
		raw_term rt300(raw_term::REL, t_arith_op::NOP, {e90, e2, e33, e118, e3, });
		rt300.neg = false;
		sprawformtree ft299 = std::make_shared<raw_form_tree>(rt300);
		sprawformtree ft293 = std::make_shared<raw_form_tree>(elem::AND, ft294, ft299);
		raw_term rt302(raw_term::REL, t_arith_op::NOP, {e125, e2, e33, e233, e3, });
		rt302.neg = false;
		sprawformtree ft301 = std::make_shared<raw_form_tree>(rt302);
		sprawformtree ft292 = std::make_shared<raw_form_tree>(elem::AND, ft293, ft301);
		raw_term rt304(raw_term::REL, t_arith_op::NOP, {e36, e2, e126, e233, e19, e3, });
		rt304.neg = false;
		sprawformtree ft303 = std::make_shared<raw_form_tree>(rt304);
		sprawformtree ft291 = std::make_shared<raw_form_tree>(elem::AND, ft292, ft303);
		raw_rule rr305({rt290, }, ft291);
		raw_term rt306(raw_term::REL, t_arith_op::NOP, {e36, e2, e17, e33, e19, e3, });
		rt306.neg = false;
		raw_term rt310(raw_term::REL, t_arith_op::NOP, {e100, e2, e17, e3, });
		rt310.neg = false;
		sprawformtree ft309 = std::make_shared<raw_form_tree>(rt310);
		raw_term rt312(raw_term::REL, t_arith_op::NOP, {e100, e2, e33, e3, });
		rt312.neg = false;
		sprawformtree ft311 = std::make_shared<raw_form_tree>(rt312);
		sprawformtree ft308 = std::make_shared<raw_form_tree>(elem::AND, ft309, ft311);
		raw_term rt314(raw_term::REL, t_arith_op::NOP, {e100, e2, e19, e3, });
		rt314.neg = false;
		sprawformtree ft313 = std::make_shared<raw_form_tree>(rt314);
		sprawformtree ft307 = std::make_shared<raw_form_tree>(elem::AND, ft308, ft313);
		raw_rule rr315({rt306, }, ft307);
		raw_term rt316(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e41, e19, e3, });
		rt316.neg = true;
		raw_term rt317(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt317.neg = true;
		raw_term rt318(raw_term::REL, t_arith_op::NOP, {e67, e2, e40, e52, e3, });
		rt318.neg = true;
		raw_term rt320(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt320.neg = false;
		sprawformtree ft319 = std::make_shared<raw_form_tree>(rt320);
		raw_rule rr321({rt316, rt317, rt318, }, ft319);
		raw_term rt322(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt322.neg = false;
		raw_term rt327(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt327.neg = false;
		sprawformtree ft326 = std::make_shared<raw_form_tree>(rt327);
		elem e329(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_type"));
		raw_term rt330(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e113, e3, });
		rt330.neg = false;
		sprawformtree ft328 = std::make_shared<raw_form_tree>(rt330);
		sprawformtree ft325 = std::make_shared<raw_form_tree>(elem::AND, ft326, ft328);
		elem e332(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_max"));
		raw_term rt333(raw_term::REL, t_arith_op::NOP, {e332, e2, e19, e3, });
		rt333.neg = false;
		sprawformtree ft331 = std::make_shared<raw_form_tree>(rt333);
		sprawformtree ft324 = std::make_shared<raw_form_tree>(elem::AND, ft325, ft331);
		raw_term rt335(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt335.neg = false;
		sprawformtree ft334 = std::make_shared<raw_form_tree>(rt335);
		sprawformtree ft323 = std::make_shared<raw_form_tree>(elem::AND, ft324, ft334);
		raw_rule rr336({rt322, }, ft323);
		raw_term rt337(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt337.neg = false;
		raw_term rt344(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt344.neg = false;
		sprawformtree ft343 = std::make_shared<raw_form_tree>(rt344);
		elem e346(int_t(6));
		raw_term rt347(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e346, e3, });
		rt347.neg = false;
		sprawformtree ft345 = std::make_shared<raw_form_tree>(rt347);
		sprawformtree ft342 = std::make_shared<raw_form_tree>(elem::AND, ft343, ft345);
		elem e349(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_not_body"));
		elem e350(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qb"));
		raw_term rt351(raw_term::REL, t_arith_op::NOP, {e349, e2, e41, e350, e3, });
		rt351.neg = false;
		sprawformtree ft348 = std::make_shared<raw_form_tree>(rt351);
		sprawformtree ft341 = std::make_shared<raw_form_tree>(elem::AND, ft342, ft348);
		raw_term rt354(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e350, e19, e3, });
		rt354.neg = false;
		sprawformtree ft353 = std::make_shared<raw_form_tree>(rt354);
		sprawformtree ft352 = std::make_shared<raw_form_tree>(elem::NOT, ft353);
		sprawformtree ft340 = std::make_shared<raw_form_tree>(elem::AND, ft341, ft352);
		raw_term rt356(raw_term::REL, t_arith_op::NOP, {e332, e2, e19, e3, });
		rt356.neg = false;
		sprawformtree ft355 = std::make_shared<raw_form_tree>(rt356);
		sprawformtree ft339 = std::make_shared<raw_form_tree>(elem::AND, ft340, ft355);
		raw_term rt358(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt358.neg = false;
		sprawformtree ft357 = std::make_shared<raw_form_tree>(rt358);
		sprawformtree ft338 = std::make_shared<raw_form_tree>(elem::AND, ft339, ft357);
		raw_rule rr359({rt337, }, ft338);
		raw_term rt360(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt360.neg = false;
		elem e367(int_t(7));
		raw_term rt368(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e367, e3, });
		rt368.neg = false;
		sprawformtree ft366 = std::make_shared<raw_form_tree>(rt368);
		elem e370(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_and_left"));
		elem e371(elem::VAR, t_arith_op::NOP, d.get_lexeme("?ql"));
		raw_term rt372(raw_term::REL, t_arith_op::NOP, {e370, e2, e41, e371, e3, });
		rt372.neg = false;
		sprawformtree ft369 = std::make_shared<raw_form_tree>(rt372);
		sprawformtree ft365 = std::make_shared<raw_form_tree>(elem::AND, ft366, ft369);
		elem e374(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_and_right"));
		elem e375(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qr"));
		raw_term rt376(raw_term::REL, t_arith_op::NOP, {e374, e2, e41, e375, e3, });
		rt376.neg = false;
		sprawformtree ft373 = std::make_shared<raw_form_tree>(rt376);
		sprawformtree ft364 = std::make_shared<raw_form_tree>(elem::AND, ft365, ft373);
		raw_term rt378(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e371, e19, e3, });
		rt378.neg = false;
		sprawformtree ft377 = std::make_shared<raw_form_tree>(rt378);
		sprawformtree ft363 = std::make_shared<raw_form_tree>(elem::AND, ft364, ft377);
		raw_term rt380(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e375, e19, e3, });
		rt380.neg = false;
		sprawformtree ft379 = std::make_shared<raw_form_tree>(rt380);
		sprawformtree ft362 = std::make_shared<raw_form_tree>(elem::AND, ft363, ft379);
		raw_term rt382(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt382.neg = false;
		sprawformtree ft381 = std::make_shared<raw_form_tree>(rt382);
		sprawformtree ft361 = std::make_shared<raw_form_tree>(elem::AND, ft362, ft381);
		raw_rule rr383({rt360, }, ft361);
		raw_term rt384(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt384.neg = false;
		elem e390(int_t(8));
		raw_term rt391(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e390, e3, });
		rt391.neg = false;
		sprawformtree ft389 = std::make_shared<raw_form_tree>(rt391);
		elem e393(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_or_left"));
		raw_term rt394(raw_term::REL, t_arith_op::NOP, {e393, e2, e41, e371, e3, });
		rt394.neg = false;
		sprawformtree ft392 = std::make_shared<raw_form_tree>(rt394);
		sprawformtree ft388 = std::make_shared<raw_form_tree>(elem::AND, ft389, ft392);
		elem e396(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_or_right"));
		raw_term rt397(raw_term::REL, t_arith_op::NOP, {e396, e2, e41, e375, e3, });
		rt397.neg = false;
		sprawformtree ft395 = std::make_shared<raw_form_tree>(rt397);
		sprawformtree ft387 = std::make_shared<raw_form_tree>(elem::AND, ft388, ft395);
		raw_term rt399(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e371, e19, e3, });
		rt399.neg = false;
		sprawformtree ft398 = std::make_shared<raw_form_tree>(rt399);
		sprawformtree ft386 = std::make_shared<raw_form_tree>(elem::AND, ft387, ft398);
		raw_term rt401(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt401.neg = false;
		sprawformtree ft400 = std::make_shared<raw_form_tree>(rt401);
		sprawformtree ft385 = std::make_shared<raw_form_tree>(elem::AND, ft386, ft400);
		raw_rule rr402({rt384, }, ft385);
		raw_term rt403(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt403.neg = false;
		raw_term rt409(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e390, e3, });
		rt409.neg = false;
		sprawformtree ft408 = std::make_shared<raw_form_tree>(rt409);
		raw_term rt411(raw_term::REL, t_arith_op::NOP, {e393, e2, e41, e371, e3, });
		rt411.neg = false;
		sprawformtree ft410 = std::make_shared<raw_form_tree>(rt411);
		sprawformtree ft407 = std::make_shared<raw_form_tree>(elem::AND, ft408, ft410);
		raw_term rt413(raw_term::REL, t_arith_op::NOP, {e396, e2, e41, e375, e3, });
		rt413.neg = false;
		sprawformtree ft412 = std::make_shared<raw_form_tree>(rt413);
		sprawformtree ft406 = std::make_shared<raw_form_tree>(elem::AND, ft407, ft412);
		raw_term rt415(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e375, e19, e3, });
		rt415.neg = false;
		sprawformtree ft414 = std::make_shared<raw_form_tree>(rt415);
		sprawformtree ft405 = std::make_shared<raw_form_tree>(elem::AND, ft406, ft414);
		raw_term rt417(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt417.neg = false;
		sprawformtree ft416 = std::make_shared<raw_form_tree>(rt417);
		sprawformtree ft404 = std::make_shared<raw_form_tree>(elem::AND, ft405, ft416);
		raw_rule rr418({rt403, }, ft404);
		raw_term rt419(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt419.neg = false;
		elem e432(int_t(2));
		raw_term rt433(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e432, e3, });
		rt433.neg = false;
		sprawformtree ft431 = std::make_shared<raw_form_tree>(rt433);
		elem e435(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_term_relation"));
		raw_term rt436(raw_term::REL, t_arith_op::NOP, {e435, e2, e41, e45, e3, });
		rt436.neg = false;
		sprawformtree ft434 = std::make_shared<raw_form_tree>(rt436);
		sprawformtree ft430 = std::make_shared<raw_form_tree>(elem::AND, ft431, ft434);
		elem e438(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_term_params"));
		elem e439(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vars"));
		raw_term rt440(raw_term::REL, t_arith_op::NOP, {e438, e2, e41, e439, e3, });
		rt440.neg = false;
		sprawformtree ft437 = std::make_shared<raw_form_tree>(rt440);
		sprawformtree ft429 = std::make_shared<raw_form_tree>(elem::AND, ft430, ft437);
		elem e442(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_term_param_types"));
		raw_term rt443(raw_term::REL, t_arith_op::NOP, {e442, e2, e41, e33, e3, });
		rt443.neg = false;
		sprawformtree ft441 = std::make_shared<raw_form_tree>(rt443);
		sprawformtree ft428 = std::make_shared<raw_form_tree>(elem::AND, ft429, ft441);
		raw_term rt445(raw_term::REL, t_arith_op::NOP, {e61, e2, e40, e45, e29, e3, });
		rt445.neg = false;
		sprawformtree ft444 = std::make_shared<raw_form_tree>(rt445);
		sprawformtree ft427 = std::make_shared<raw_form_tree>(elem::AND, ft428, ft444);
		raw_term rt447(raw_term::REL, t_arith_op::NOP, {e332, e2, e19, e3, });
		rt447.neg = false;
		sprawformtree ft446 = std::make_shared<raw_form_tree>(rt447);
		sprawformtree ft426 = std::make_shared<raw_form_tree>(elem::AND, ft427, ft446);
		elem e449(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vars_s"));
		raw_term rt450(raw_term::REL, t_arith_op::NOP, {e32, e2, e439, e33, e449, e3, });
		rt450.neg = false;
		sprawformtree ft448 = std::make_shared<raw_form_tree>(rt450);
		sprawformtree ft425 = std::make_shared<raw_form_tree>(elem::AND, ft426, ft448);
		elem e452(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals_s"));
		raw_term rt453(raw_term::REL, t_arith_op::NOP, {e32, e2, e29, e33, e452, e3, });
		rt453.neg = false;
		sprawformtree ft451 = std::make_shared<raw_form_tree>(rt453);
		sprawformtree ft424 = std::make_shared<raw_form_tree>(elem::AND, ft425, ft451);
		raw_term rt455(raw_term::REL, t_arith_op::NOP, {e26, e2, e19, e449, e452, e3, });
		rt455.neg = false;
		sprawformtree ft454 = std::make_shared<raw_form_tree>(rt455);
		sprawformtree ft423 = std::make_shared<raw_form_tree>(elem::AND, ft424, ft454);
		elem e457(elem::VAR, t_arith_op::NOP, d.get_lexeme("?syms"));
		raw_term rt458(raw_term::REL, t_arith_op::NOP, {e36, e2, e439, e33, e457, e3, });
		rt458.neg = false;
		sprawformtree ft456 = std::make_shared<raw_form_tree>(rt458);
		sprawformtree ft422 = std::make_shared<raw_form_tree>(elem::AND, ft423, ft456);
		raw_term rt460(raw_term::REL, t_arith_op::NOP, {e36, e2, e29, e33, e457, e3, });
		rt460.neg = false;
		sprawformtree ft459 = std::make_shared<raw_form_tree>(rt460);
		sprawformtree ft421 = std::make_shared<raw_form_tree>(elem::AND, ft422, ft459);
		raw_term rt462(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt462.neg = false;
		sprawformtree ft461 = std::make_shared<raw_form_tree>(rt462);
		sprawformtree ft420 = std::make_shared<raw_form_tree>(elem::AND, ft421, ft461);
		raw_rule rr463({rt419, }, ft420);
		raw_term rt464(raw_term::REL, t_arith_op::NOP, {e44, e2, e40, e45, e19, e3, });
		rt464.neg = false;
		raw_term rt479(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e118, e3, });
		rt479.neg = false;
		sprawformtree ft478 = std::make_shared<raw_form_tree>(rt479);
		elem e481(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_rule_head"));
		elem e482(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qh"));
		raw_term rt483(raw_term::REL, t_arith_op::NOP, {e481, e2, e41, e482, e3, });
		rt483.neg = false;
		sprawformtree ft480 = std::make_shared<raw_form_tree>(rt483);
		sprawformtree ft477 = std::make_shared<raw_form_tree>(elem::AND, ft478, ft480);
		elem e485(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_rule_body"));
		raw_term rt486(raw_term::REL, t_arith_op::NOP, {e485, e2, e41, e350, e3, });
		rt486.neg = false;
		sprawformtree ft484 = std::make_shared<raw_form_tree>(rt486);
		sprawformtree ft476 = std::make_shared<raw_form_tree>(elem::AND, ft477, ft484);
		raw_term rt488(raw_term::REL, t_arith_op::NOP, {e329, e2, e482, e432, e3, });
		rt488.neg = false;
		sprawformtree ft487 = std::make_shared<raw_form_tree>(rt488);
		sprawformtree ft475 = std::make_shared<raw_form_tree>(elem::AND, ft476, ft487);
		raw_term rt490(raw_term::REL, t_arith_op::NOP, {e435, e2, e482, e45, e3, });
		rt490.neg = false;
		sprawformtree ft489 = std::make_shared<raw_form_tree>(rt490);
		sprawformtree ft474 = std::make_shared<raw_form_tree>(elem::AND, ft475, ft489);
		raw_term rt492(raw_term::REL, t_arith_op::NOP, {e438, e2, e482, e439, e3, });
		rt492.neg = false;
		sprawformtree ft491 = std::make_shared<raw_form_tree>(rt492);
		sprawformtree ft473 = std::make_shared<raw_form_tree>(elem::AND, ft474, ft491);
		raw_term rt494(raw_term::REL, t_arith_op::NOP, {e442, e2, e482, e33, e3, });
		rt494.neg = false;
		sprawformtree ft493 = std::make_shared<raw_form_tree>(rt494);
		sprawformtree ft472 = std::make_shared<raw_form_tree>(elem::AND, ft473, ft493);
		raw_term rt496(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e350, e29, e3, });
		rt496.neg = false;
		sprawformtree ft495 = std::make_shared<raw_form_tree>(rt496);
		sprawformtree ft471 = std::make_shared<raw_form_tree>(elem::AND, ft472, ft495);
		raw_term rt498(raw_term::REL, t_arith_op::NOP, {e32, e2, e439, e33, e449, e3, });
		rt498.neg = false;
		sprawformtree ft497 = std::make_shared<raw_form_tree>(rt498);
		sprawformtree ft470 = std::make_shared<raw_form_tree>(elem::AND, ft471, ft497);
		elem e500(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out_s"));
		raw_term rt501(raw_term::REL, t_arith_op::NOP, {e32, e2, e19, e33, e500, e3, });
		rt501.neg = false;
		sprawformtree ft499 = std::make_shared<raw_form_tree>(rt501);
		sprawformtree ft469 = std::make_shared<raw_form_tree>(elem::AND, ft470, ft499);
		raw_term rt503(raw_term::REL, t_arith_op::NOP, {e26, e2, e29, e449, e500, e3, });
		rt503.neg = false;
		sprawformtree ft502 = std::make_shared<raw_form_tree>(rt503);
		sprawformtree ft468 = std::make_shared<raw_form_tree>(elem::AND, ft469, ft502);
		raw_term rt505(raw_term::REL, t_arith_op::NOP, {e36, e2, e439, e33, e457, e3, });
		rt505.neg = false;
		sprawformtree ft504 = std::make_shared<raw_form_tree>(rt505);
		sprawformtree ft467 = std::make_shared<raw_form_tree>(elem::AND, ft468, ft504);
		raw_term rt507(raw_term::REL, t_arith_op::NOP, {e36, e2, e19, e33, e457, e3, });
		rt507.neg = false;
		sprawformtree ft506 = std::make_shared<raw_form_tree>(rt507);
		sprawformtree ft466 = std::make_shared<raw_form_tree>(elem::AND, ft467, ft506);
		raw_term rt509(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt509.neg = false;
		sprawformtree ft508 = std::make_shared<raw_form_tree>(rt509);
		sprawformtree ft465 = std::make_shared<raw_form_tree>(elem::AND, ft466, ft508);
		raw_rule rr510({rt464, }, ft465);
		raw_term rt511(raw_term::REL, t_arith_op::NOP, {e48, e2, e40, e45, e19, e3, });
		rt511.neg = false;
		raw_term rt528(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e118, e3, });
		rt528.neg = false;
		sprawformtree ft527 = std::make_shared<raw_form_tree>(rt528);
		elem e530(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qnh"));
		raw_term rt531(raw_term::REL, t_arith_op::NOP, {e481, e2, e41, e530, e3, });
		rt531.neg = false;
		sprawformtree ft529 = std::make_shared<raw_form_tree>(rt531);
		sprawformtree ft526 = std::make_shared<raw_form_tree>(elem::AND, ft527, ft529);
		raw_term rt533(raw_term::REL, t_arith_op::NOP, {e485, e2, e41, e350, e3, });
		rt533.neg = false;
		sprawformtree ft532 = std::make_shared<raw_form_tree>(rt533);
		sprawformtree ft525 = std::make_shared<raw_form_tree>(elem::AND, ft526, ft532);
		raw_term rt535(raw_term::REL, t_arith_op::NOP, {e329, e2, e530, e346, e3, });
		rt535.neg = false;
		sprawformtree ft534 = std::make_shared<raw_form_tree>(rt535);
		sprawformtree ft524 = std::make_shared<raw_form_tree>(elem::AND, ft525, ft534);
		raw_term rt537(raw_term::REL, t_arith_op::NOP, {e349, e2, e530, e482, e3, });
		rt537.neg = false;
		sprawformtree ft536 = std::make_shared<raw_form_tree>(rt537);
		sprawformtree ft523 = std::make_shared<raw_form_tree>(elem::AND, ft524, ft536);
		raw_term rt539(raw_term::REL, t_arith_op::NOP, {e329, e2, e482, e432, e3, });
		rt539.neg = false;
		sprawformtree ft538 = std::make_shared<raw_form_tree>(rt539);
		sprawformtree ft522 = std::make_shared<raw_form_tree>(elem::AND, ft523, ft538);
		raw_term rt541(raw_term::REL, t_arith_op::NOP, {e435, e2, e482, e45, e3, });
		rt541.neg = false;
		sprawformtree ft540 = std::make_shared<raw_form_tree>(rt541);
		sprawformtree ft521 = std::make_shared<raw_form_tree>(elem::AND, ft522, ft540);
		raw_term rt543(raw_term::REL, t_arith_op::NOP, {e438, e2, e482, e439, e3, });
		rt543.neg = false;
		sprawformtree ft542 = std::make_shared<raw_form_tree>(rt543);
		sprawformtree ft520 = std::make_shared<raw_form_tree>(elem::AND, ft521, ft542);
		raw_term rt545(raw_term::REL, t_arith_op::NOP, {e442, e2, e482, e33, e3, });
		rt545.neg = false;
		sprawformtree ft544 = std::make_shared<raw_form_tree>(rt545);
		sprawformtree ft519 = std::make_shared<raw_form_tree>(elem::AND, ft520, ft544);
		raw_term rt547(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e350, e29, e3, });
		rt547.neg = false;
		sprawformtree ft546 = std::make_shared<raw_form_tree>(rt547);
		sprawformtree ft518 = std::make_shared<raw_form_tree>(elem::AND, ft519, ft546);
		raw_term rt549(raw_term::REL, t_arith_op::NOP, {e32, e2, e439, e33, e449, e3, });
		rt549.neg = false;
		sprawformtree ft548 = std::make_shared<raw_form_tree>(rt549);
		sprawformtree ft517 = std::make_shared<raw_form_tree>(elem::AND, ft518, ft548);
		raw_term rt551(raw_term::REL, t_arith_op::NOP, {e32, e2, e19, e33, e500, e3, });
		rt551.neg = false;
		sprawformtree ft550 = std::make_shared<raw_form_tree>(rt551);
		sprawformtree ft516 = std::make_shared<raw_form_tree>(elem::AND, ft517, ft550);
		raw_term rt553(raw_term::REL, t_arith_op::NOP, {e26, e2, e29, e449, e500, e3, });
		rt553.neg = false;
		sprawformtree ft552 = std::make_shared<raw_form_tree>(rt553);
		sprawformtree ft515 = std::make_shared<raw_form_tree>(elem::AND, ft516, ft552);
		raw_term rt555(raw_term::REL, t_arith_op::NOP, {e36, e2, e439, e33, e457, e3, });
		rt555.neg = false;
		sprawformtree ft554 = std::make_shared<raw_form_tree>(rt555);
		sprawformtree ft514 = std::make_shared<raw_form_tree>(elem::AND, ft515, ft554);
		raw_term rt557(raw_term::REL, t_arith_op::NOP, {e36, e2, e19, e33, e457, e3, });
		rt557.neg = false;
		sprawformtree ft556 = std::make_shared<raw_form_tree>(rt557);
		sprawformtree ft513 = std::make_shared<raw_form_tree>(elem::AND, ft514, ft556);
		raw_term rt559(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt559.neg = false;
		sprawformtree ft558 = std::make_shared<raw_form_tree>(rt559);
		sprawformtree ft512 = std::make_shared<raw_form_tree>(elem::AND, ft513, ft558);
		raw_rule rr560({rt511, }, ft512);
		raw_term rt561(raw_term::REL, t_arith_op::NOP, {e51, e2, e52, e45, e19, e3, });
		rt561.neg = false;
		raw_term rt564(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt564.neg = false;
		sprawformtree ft563 = std::make_shared<raw_form_tree>(rt564);
		raw_term rt566(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt566.neg = false;
		sprawformtree ft565 = std::make_shared<raw_form_tree>(rt566);
		sprawformtree ft562 = std::make_shared<raw_form_tree>(elem::AND, ft563, ft565);
		raw_rule rr567({rt561, }, ft562);
		raw_term rt568(raw_term::REL, t_arith_op::NOP, {e55, e2, e40, e52, e3, });
		rt568.neg = false;
		elem e576(elem::LT, t_arith_op::NOP, d.get_lexeme("<"));
		raw_term rt577(raw_term::LEQ, t_arith_op::NOP, {e52, e576, e40, });
		rt577.neg = false;
		sprawformtree ft575 = std::make_shared<raw_form_tree>(rt577);
		sprawformtree ft574 = std::make_shared<raw_form_tree>(elem::NOT, ft575);
		raw_term rt579(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt579.neg = false;
		sprawformtree ft578 = std::make_shared<raw_form_tree>(rt579);
		sprawformtree ft573 = std::make_shared<raw_form_tree>(elem::AND, ft574, ft578);
		raw_term rt581(raw_term::REL, t_arith_op::NOP, {e58, e2, e52, e3, });
		rt581.neg = false;
		sprawformtree ft580 = std::make_shared<raw_form_tree>(rt581);
		sprawformtree ft572 = std::make_shared<raw_form_tree>(elem::AND, ft573, ft580);
		raw_term rt583(raw_term::REL, t_arith_op::NOP, {e61, e2, e40, e45, e19, e3, });
		rt583.neg = false;
		sprawformtree ft582 = std::make_shared<raw_form_tree>(rt583);
		sprawformtree ft571 = std::make_shared<raw_form_tree>(elem::AND, ft572, ft582);
		raw_term rt586(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt586.neg = false;
		sprawformtree ft585 = std::make_shared<raw_form_tree>(rt586);
		sprawformtree ft584 = std::make_shared<raw_form_tree>(elem::NOT, ft585);
		sprawformtree ft570 = std::make_shared<raw_form_tree>(elem::AND, ft571, ft584);
		raw_term rt588(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt588.neg = false;
		sprawformtree ft587 = std::make_shared<raw_form_tree>(rt588);
		sprawformtree ft569 = std::make_shared<raw_form_tree>(elem::AND, ft570, ft587);
		raw_rule rr589({rt568, }, ft569);
		raw_term rt590(raw_term::REL, t_arith_op::NOP, {e55, e2, e40, e52, e3, });
		rt590.neg = false;
		raw_term rt598(raw_term::LEQ, t_arith_op::NOP, {e52, e576, e40, });
		rt598.neg = false;
		sprawformtree ft597 = std::make_shared<raw_form_tree>(rt598);
		sprawformtree ft596 = std::make_shared<raw_form_tree>(elem::NOT, ft597);
		raw_term rt600(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt600.neg = false;
		sprawformtree ft599 = std::make_shared<raw_form_tree>(rt600);
		sprawformtree ft595 = std::make_shared<raw_form_tree>(elem::AND, ft596, ft599);
		raw_term rt602(raw_term::REL, t_arith_op::NOP, {e58, e2, e52, e3, });
		rt602.neg = false;
		sprawformtree ft601 = std::make_shared<raw_form_tree>(rt602);
		sprawformtree ft594 = std::make_shared<raw_form_tree>(elem::AND, ft595, ft601);
		raw_term rt605(raw_term::REL, t_arith_op::NOP, {e61, e2, e40, e45, e19, e3, });
		rt605.neg = false;
		sprawformtree ft604 = std::make_shared<raw_form_tree>(rt605);
		sprawformtree ft603 = std::make_shared<raw_form_tree>(elem::NOT, ft604);
		sprawformtree ft593 = std::make_shared<raw_form_tree>(elem::AND, ft594, ft603);
		raw_term rt607(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt607.neg = false;
		sprawformtree ft606 = std::make_shared<raw_form_tree>(rt607);
		sprawformtree ft592 = std::make_shared<raw_form_tree>(elem::AND, ft593, ft606);
		raw_term rt609(raw_term::REL, t_arith_op::NOP, {e1, e2, e3, });
		rt609.neg = false;
		sprawformtree ft608 = std::make_shared<raw_form_tree>(rt609);
		sprawformtree ft591 = std::make_shared<raw_form_tree>(elem::AND, ft592, ft608);
		raw_rule rr610({rt590, }, ft591);
		raw_term rt611(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt611.neg = true;
		raw_term rt612(raw_term::REL, t_arith_op::NOP, {e44, e2, e40, e45, e19, e3, });
		rt612.neg = true;
		raw_term rt613(raw_term::REL, t_arith_op::NOP, {e48, e2, e40, e45, e19, e3, });
		rt613.neg = true;
		raw_term rt614(raw_term::REL, t_arith_op::NOP, {e51, e2, e52, e45, e19, e3, });
		rt614.neg = true;
		raw_term rt615(raw_term::REL, t_arith_op::NOP, {e55, e2, e40, e52, e3, });
		rt615.neg = true;
		raw_term rt617(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt617.neg = false;
		sprawformtree ft616 = std::make_shared<raw_form_tree>(rt617);
		raw_rule rr618({rt611, rt612, rt613, rt614, rt615, }, ft616);
		raw_term rt619(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt619.neg = false;
		elem e623(elem::LEQ, t_arith_op::NOP, d.get_lexeme("<="));
		raw_term rt624(raw_term::LEQ, t_arith_op::NOP, {e113, e623, e40, });
		rt624.neg = false;
		sprawformtree ft622 = std::make_shared<raw_form_tree>(rt624);
		elem e627(timeout);
		raw_term rt628(raw_term::LEQ, t_arith_op::NOP, {e627, e576, e40, });
		rt628.neg = false;
		sprawformtree ft626 = std::make_shared<raw_form_tree>(rt628);
		sprawformtree ft625 = std::make_shared<raw_form_tree>(elem::NOT, ft626);
		sprawformtree ft621 = std::make_shared<raw_form_tree>(elem::AND, ft622, ft625);
		raw_term rt630(raw_term::ARITH, t_arith_op::ADD, {e40, e117, e113, e119, e40, });
		rt630.neg = false;
		sprawformtree ft629 = std::make_shared<raw_form_tree>(rt630);
		sprawformtree ft620 = std::make_shared<raw_form_tree>(elem::AND, ft621, ft629);
		raw_rule rr631({rt619, }, ft620);
		raw_term rt632(raw_term::REL, t_arith_op::NOP, {e61, e2, e113, e45, e19, e3, });
		rt632.neg = false;
		raw_term rt643(raw_term::REL, t_arith_op::NOP, {e329, e2, e41, e113, e3, });
		rt643.neg = false;
		sprawformtree ft642 = std::make_shared<raw_form_tree>(rt643);
		elem e645(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_fact_term"));
		elem e646(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qt"));
		raw_term rt647(raw_term::REL, t_arith_op::NOP, {e645, e2, e41, e646, e3, });
		rt647.neg = false;
		sprawformtree ft644 = std::make_shared<raw_form_tree>(rt647);
		sprawformtree ft641 = std::make_shared<raw_form_tree>(elem::AND, ft642, ft644);
		raw_term rt649(raw_term::REL, t_arith_op::NOP, {e329, e2, e646, e432, e3, });
		rt649.neg = false;
		sprawformtree ft648 = std::make_shared<raw_form_tree>(rt649);
		sprawformtree ft640 = std::make_shared<raw_form_tree>(elem::AND, ft641, ft648);
		raw_term rt651(raw_term::REL, t_arith_op::NOP, {e435, e2, e646, e45, e3, });
		rt651.neg = false;
		sprawformtree ft650 = std::make_shared<raw_form_tree>(rt651);
		sprawformtree ft639 = std::make_shared<raw_form_tree>(elem::AND, ft640, ft650);
		raw_term rt653(raw_term::REL, t_arith_op::NOP, {e438, e2, e646, e439, e3, });
		rt653.neg = false;
		sprawformtree ft652 = std::make_shared<raw_form_tree>(rt653);
		sprawformtree ft638 = std::make_shared<raw_form_tree>(elem::AND, ft639, ft652);
		raw_term rt655(raw_term::REL, t_arith_op::NOP, {e442, e2, e646, e33, e3, });
		rt655.neg = false;
		sprawformtree ft654 = std::make_shared<raw_form_tree>(rt655);
		sprawformtree ft637 = std::make_shared<raw_form_tree>(elem::AND, ft638, ft654);
		raw_term rt657(raw_term::REL, t_arith_op::NOP, {e13, e2, e19, e3, });
		rt657.neg = false;
		sprawformtree ft656 = std::make_shared<raw_form_tree>(rt657);
		sprawformtree ft636 = std::make_shared<raw_form_tree>(elem::AND, ft637, ft656);
		raw_term rt659(raw_term::REL, t_arith_op::NOP, {e36, e2, e439, e33, e457, e3, });
		rt659.neg = false;
		sprawformtree ft658 = std::make_shared<raw_form_tree>(rt659);
		sprawformtree ft635 = std::make_shared<raw_form_tree>(elem::AND, ft636, ft658);
		raw_term rt661(raw_term::REL, t_arith_op::NOP, {e36, e2, e19, e33, e457, e3, });
		rt661.neg = false;
		sprawformtree ft660 = std::make_shared<raw_form_tree>(rt661);
		sprawformtree ft634 = std::make_shared<raw_form_tree>(elem::AND, ft635, ft660);
		raw_term rt663(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt663.neg = false;
		sprawformtree ft662 = std::make_shared<raw_form_tree>(rt663);
		sprawformtree ft633 = std::make_shared<raw_form_tree>(elem::AND, ft634, ft662);
		raw_rule rr664({rt632, }, ft633);
		raw_term rt665(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt665.neg = false;
		raw_term rt670(raw_term::ARITH, t_arith_op::ADD, {e40, e117, e118, e119, e52, });
		rt670.neg = false;
		sprawformtree ft669 = std::make_shared<raw_form_tree>(rt670);
		raw_term rt672(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt672.neg = false;
		sprawformtree ft671 = std::make_shared<raw_form_tree>(rt672);
		sprawformtree ft668 = std::make_shared<raw_form_tree>(elem::AND, ft669, ft671);
		raw_term rt674(raw_term::REL, t_arith_op::NOP, {e44, e2, e40, e45, e19, e3, });
		rt674.neg = false;
		sprawformtree ft673 = std::make_shared<raw_form_tree>(rt674);
		sprawformtree ft667 = std::make_shared<raw_form_tree>(elem::AND, ft668, ft673);
		raw_term rt676(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt676.neg = false;
		sprawformtree ft675 = std::make_shared<raw_form_tree>(rt676);
		sprawformtree ft666 = std::make_shared<raw_form_tree>(elem::AND, ft667, ft675);
		raw_rule rr677({rt665, }, ft666);
		raw_term rt678(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt678.neg = false;
		raw_term rt684(raw_term::ARITH, t_arith_op::ADD, {e40, e117, e118, e119, e52, });
		rt684.neg = false;
		sprawformtree ft683 = std::make_shared<raw_form_tree>(rt684);
		raw_term rt686(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt686.neg = false;
		sprawformtree ft685 = std::make_shared<raw_form_tree>(rt686);
		sprawformtree ft682 = std::make_shared<raw_form_tree>(elem::AND, ft683, ft685);
		raw_term rt689(raw_term::REL, t_arith_op::NOP, {e48, e2, e40, e45, e19, e3, });
		rt689.neg = false;
		sprawformtree ft688 = std::make_shared<raw_form_tree>(rt689);
		sprawformtree ft687 = std::make_shared<raw_form_tree>(elem::NOT, ft688);
		sprawformtree ft681 = std::make_shared<raw_form_tree>(elem::AND, ft682, ft687);
		raw_term rt691(raw_term::REL, t_arith_op::NOP, {e51, e2, e40, e45, e19, e3, });
		rt691.neg = false;
		sprawformtree ft690 = std::make_shared<raw_form_tree>(rt691);
		sprawformtree ft680 = std::make_shared<raw_form_tree>(elem::AND, ft681, ft690);
		raw_term rt693(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt693.neg = false;
		sprawformtree ft692 = std::make_shared<raw_form_tree>(rt693);
		sprawformtree ft679 = std::make_shared<raw_form_tree>(elem::AND, ft680, ft692);
		raw_rule rr694({rt678, }, ft679);
		raw_term rt695(raw_term::REL, t_arith_op::NOP, {e61, e2, e52, e45, e19, e3, });
		rt695.neg = true;
		raw_term rt700(raw_term::ARITH, t_arith_op::ADD, {e40, e117, e118, e119, e52, });
		rt700.neg = false;
		sprawformtree ft699 = std::make_shared<raw_form_tree>(rt700);
		raw_term rt702(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt702.neg = false;
		sprawformtree ft701 = std::make_shared<raw_form_tree>(rt702);
		sprawformtree ft698 = std::make_shared<raw_form_tree>(elem::AND, ft699, ft701);
		raw_term rt704(raw_term::REL, t_arith_op::NOP, {e48, e2, e40, e45, e19, e3, });
		rt704.neg = false;
		sprawformtree ft703 = std::make_shared<raw_form_tree>(rt704);
		sprawformtree ft697 = std::make_shared<raw_form_tree>(elem::AND, ft698, ft703);
		raw_term rt706(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt706.neg = false;
		sprawformtree ft705 = std::make_shared<raw_form_tree>(rt706);
		sprawformtree ft696 = std::make_shared<raw_form_tree>(elem::AND, ft697, ft705);
		raw_rule rr707({rt695, }, ft696);
		raw_term rt708(raw_term::REL, t_arith_op::NOP, {e64, e2, e40, e41, e19, e3, });
		rt708.neg = false;
		raw_term rt711(raw_term::REL, t_arith_op::NOP, {e39, e2, e40, e41, e19, e3, });
		rt711.neg = false;
		sprawformtree ft710 = std::make_shared<raw_form_tree>(rt711);
		raw_term rt713(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt713.neg = false;
		sprawformtree ft712 = std::make_shared<raw_form_tree>(rt713);
		sprawformtree ft709 = std::make_shared<raw_form_tree>(elem::AND, ft710, ft712);
		raw_rule rr714({rt708, }, ft709);
		raw_term rt715(raw_term::REL, t_arith_op::NOP, {e67, e2, e40, e52, e3, });
		rt715.neg = false;
		raw_term rt722(raw_term::LEQ, t_arith_op::NOP, {e52, e576, e40, });
		rt722.neg = false;
		sprawformtree ft721 = std::make_shared<raw_form_tree>(rt722);
		sprawformtree ft720 = std::make_shared<raw_form_tree>(elem::NOT, ft721);
		raw_term rt724(raw_term::REL, t_arith_op::NOP, {e58, e2, e40, e3, });
		rt724.neg = false;
		sprawformtree ft723 = std::make_shared<raw_form_tree>(rt724);
		sprawformtree ft719 = std::make_shared<raw_form_tree>(elem::AND, ft720, ft723);
		raw_term rt726(raw_term::REL, t_arith_op::NOP, {e58, e2, e52, e3, });
		rt726.neg = false;
		sprawformtree ft725 = std::make_shared<raw_form_tree>(rt726);
		sprawformtree ft718 = std::make_shared<raw_form_tree>(elem::AND, ft719, ft725);
		raw_term rt729(raw_term::REL, t_arith_op::NOP, {e55, e2, e40, e52, e3, });
		rt729.neg = false;
		sprawformtree ft728 = std::make_shared<raw_form_tree>(rt729);
		sprawformtree ft727 = std::make_shared<raw_form_tree>(elem::NOT, ft728);
		sprawformtree ft717 = std::make_shared<raw_form_tree>(elem::AND, ft718, ft727);
		raw_term rt731(raw_term::REL, t_arith_op::NOP, {e6, e2, e3, });
		rt731.neg = false;
		sprawformtree ft730 = std::make_shared<raw_form_tree>(rt731);
		sprawformtree ft716 = std::make_shared<raw_form_tree>(elem::AND, ft717, ft730);
		raw_rule rr732({rt715, }, ft716);
		raw_prog &rp733 = rp;
		rp733.r.insert(rp733.r.end(), { rr77, rr82, rr87, rr93, rr97, rr102, rr136, rr152, rr175, rr185, rr208, rr218, rr241, rr257, rr267, rr289, rr305, rr315, rr321, rr336, rr359, rr383, rr402, rr418, rr463, rr510, rr560, rr567, rr589, rr610, rr618, rr631, rr664, rr677, rr694, rr707, rr714, rr732, });
		rp733.d.insert(rp733.d.end(), { dir0, dir5, dir8, dir12, dir15, dir21, dir25, dir31, dir35, dir38, dir43, dir47, dir50, dir54, dir57, dir60, dir63, dir66, });
	}
	o::dbg() << "Generated eval for: " << drt << endl;
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

/* Applies the given transformation on the given program in post-order.
 * I.e. the transformation is applied to the nested programs first and
 * then to the program proper. */

void driver::recursive_transform(raw_prog &rp,
		const function<void(raw_prog &)> &f) {
	for(raw_prog &np : rp.nps) {
		recursive_transform(np, f);
	}
	f(rp);
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
		for(const set<const relation *> v : sorted) {
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
			raw_form_tree &prft = *rr.prft;
			// Repeatedly strip outermost existential quantifier
			while(prft.type == elem::EXISTS) {
				prft = *prft.r;
			}
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
				prft = raw_form_tree(elem::AND, make_shared<raw_form_tree>(*pprft),
					make_shared<raw_form_tree>(prft));
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

/* It is sometimes desirable to embed a large amount of TML code into
 * this C++ codebase. Unfortunately, manually writing C++ code to
 * generate a certain TML fragment can be tedious. This pseudo-
 * transformation takes TML code and automatically produces the C++ code
 * necessary to generate the TML code. This transformation is used to
 * embed TML interpreter written in TML into this codebase. */

// Generate C++ code to generate the given elem

string_t driver::generate_cpp(const elem &e, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache) {
	if(elem_cache.find(e) != elem_cache.end()) {
		return elem_cache[e];
	}
	string_t e_name = to_string_t("e") + to_string_t(to_string(cid++).c_str());
	elem_cache[e] = e_name;
	if(e.type == elem::CHR) {
		prog_constr += to_string_t("elem ") + e_name +
			to_string_t("(char32_t(") + to_string_t(to_string(e.ch).c_str()) +
			to_string_t("));\n");
	} else if(e.type == elem::NUM) {
		prog_constr += to_string_t("elem ") + e_name + to_string_t("(int_t(") +
			to_string_t(to_string(e.num).c_str()) + to_string_t("));\n");
	} else {
		prog_constr += to_string_t("elem ") + e_name + to_string_t("(") +
			to_string_t(
				e.type == elem::NONE ? "elem::NONE" :
				e.type == elem::SYM ? "elem::SYM" :
				e.type == elem::NUM ? "elem::NUM" :
				e.type == elem::CHR ? "elem::CHR" :
				e.type == elem::VAR ? "elem::VAR" :
				e.type == elem::OPENP ? "elem::OPENP" :
				e.type == elem::CLOSEP ? "elem::CLOSEP" :
				e.type == elem::ALT ? "elem::ALT" :
				e.type == elem::STR ? "elem::STR" :
				e.type == elem::EQ ? "elem::EQ" :
				e.type == elem::NEQ ? "elem::NEQ" :
				e.type == elem::LEQ ? "elem::LEQ" :
				e.type == elem::GT ? "elem::GT" :
				e.type == elem::LT ? "elem::LT" :
				e.type == elem::GEQ ? "elem::GEQ" :
				e.type == elem::BLTIN ? "elem::BLTIN" :
				e.type == elem::NOT ? "elem::NOT" :
				e.type == elem::AND ? "elem::AND" :
				e.type == elem::OR ? "elem::OR" :
				e.type == elem::FORALL ? "elem::FORALL" :
				e.type == elem::EXISTS ? "elem::EXISTS" :
				e.type == elem::UNIQUE ? "elem::UNIQUE" :
				e.type == elem::IMPLIES ? "elem::IMPLIES" :
				e.type == elem::COIMPLIES ? "elem::COIMPLIES" :
				e.type == elem::ARITH ? "elem::ARITH" :
				e.type == elem::OPENB ? "elem::OPENB" :
				e.type == elem::CLOSEB ? "elem::CLOSEB" :
				e.type == elem::OPENSB ? "elem::OPENSB" :
				e.type == elem::CLOSESB ? "elem::CLOSESB" : "") + to_string_t(", ") +
			to_string_t(
				e.arith_op == t_arith_op::NOP ? "t_arith_op::NOP" :
				e.arith_op == t_arith_op::ADD ? "t_arith_op::ADD" :
				e.arith_op == t_arith_op::SUB ? "t_arith_op::SUB" :
				e.arith_op == t_arith_op::MULT ? "t_arith_op::MULT" :
				e.arith_op == t_arith_op::BITWAND ? "t_arith_op::BITWAND" :
				e.arith_op == t_arith_op::BITWOR ? "t_arith_op::BITWOR" :
				e.arith_op == t_arith_op::BITWXOR ? "t_arith_op::BITWXOR" :
				e.arith_op == t_arith_op::BITWNOT ? "t_arith_op::BITWNOT" :
				e.arith_op == t_arith_op::SHR ? "t_arith_op::SHR" :
				e.arith_op == t_arith_op::SHL ? "t_arith_op::SHL" : "") +
			to_string_t(", ") + dict_name + to_string_t(".get_lexeme(\"") +
			lexeme2str(e.e) + to_string_t("\"));\n");
	}
	return e_name;
}

// Generate the C++ code to generate the given raw_term

string_t driver::generate_cpp(const raw_term &rt, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache) {
	vector<string_t> elem_names;
	for(const elem &e : rt.e) {
		elem_names.push_back(generate_cpp(e, prog_constr, cid, dict_name, elem_cache));
	}
	string_t rt_name = to_string_t("rt") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("raw_term ") + rt_name + to_string_t("(") +
		to_string_t(
			rt.extype == raw_term::REL ? "raw_term::REL" :
			rt.extype == raw_term::EQ ? "raw_term::EQ" :
			rt.extype == raw_term::LEQ ? "raw_term::LEQ" :
			rt.extype == raw_term::BLTIN ? "raw_term::BLTIN" :
			rt.extype == raw_term::ARITH ? "raw_term::ARITH" :
			rt.extype == raw_term::CONSTRAINT ? "raw_term::CONSTRAINT" : "") +
		to_string_t(", ") + to_string_t(
			rt.arith_op == t_arith_op::NOP ? "t_arith_op::NOP" :
			rt.arith_op == t_arith_op::ADD ? "t_arith_op::ADD" :
			rt.arith_op == t_arith_op::SUB ? "t_arith_op::SUB" :
			rt.arith_op == t_arith_op::MULT ? "t_arith_op::MULT" :
			rt.arith_op == t_arith_op::BITWAND ? "t_arith_op::BITWAND" :
			rt.arith_op == t_arith_op::BITWOR ? "t_arith_op::BITWOR" :
			rt.arith_op == t_arith_op::BITWXOR ? "t_arith_op::BITWXOR" :
			rt.arith_op == t_arith_op::BITWNOT ? "t_arith_op::BITWNOT" :
			rt.arith_op == t_arith_op::SHR ? "t_arith_op::SHR" :
			rt.arith_op == t_arith_op::SHL ? "t_arith_op::SHL" : "") +
		to_string_t(", {");
	for(const string_t &en : elem_names) {
		prog_constr += en + to_string_t(", ");
	}
	prog_constr += to_string_t("});\n");
	prog_constr += rt_name + to_string_t(".neg = ") +
		to_string_t(rt.neg ? "true" : "false") + to_string_t(";\n");
	return rt_name;
}

// Generate the C++ code to generate the raw_form_tree

string_t driver::generate_cpp(const raw_form_tree &t, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name, map<elem, string_t> &elem_cache) {
	string_t ft_name = to_string_t("ft") + to_string_t(to_string(cid++).c_str());
	switch(t.type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT: case elem::EXISTS: case elem::UNIQUE:
		case elem::FORALL: {
			string_t lft_name =
				generate_cpp(*t.l, prog_constr, cid, dict_name, elem_cache);
			string_t rft_name = generate_cpp(*t.r, prog_constr, cid, dict_name,
				elem_cache);
			string_t t_string = to_string_t(
				t.type == elem::IMPLIES ? "elem::IMPLIES" :
				t.type == elem::COIMPLIES ? "elem::COIMPLIES" :
				t.type == elem::AND ? "elem::AND" :
				t.type == elem::ALT ? "elem::ALT" :
				t.type == elem::EXISTS ? "elem::EXISTS" :
				t.type == elem::UNIQUE ? "elem::UNIQUE" :
				t.type == elem::FORALL ? "elem::FORALL" : "");
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(") + t_string + to_string_t(", ") +
				lft_name + to_string_t(", ") + rft_name + to_string_t(");\n");
			break;
		} case elem::NOT: {
			string_t body_name = generate_cpp(*t.l, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::NOT, ") +
				body_name + to_string_t(");\n");
			break;
		} case elem::NONE: {
			string_t term_name = generate_cpp(*t.rt, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(") + term_name + to_string_t(");\n");
			break;
		} case elem::VAR: {
			string_t var_name = generate_cpp(*t.el, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::VAR, ") +
				var_name + to_string_t(");\n");
			break;
		} default:
			assert(false); //should never reach here
	}
	return ft_name;
}

// Generate the C++ code to generate the given TML rule

string_t driver::generate_cpp(const raw_rule &rr, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache) {
	vector<string_t> term_names;
	for(const raw_term &rt : rr.h) {
		term_names.push_back(
			generate_cpp(rt, prog_constr, cid, dict_name, elem_cache));
	}
	string_t prft_name = generate_cpp(*rr.get_prft(),
		prog_constr, cid, dict_name, elem_cache);
	string_t rule_name = to_string_t("rr") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("raw_rule ") + rule_name + to_string_t("({");
	for(const string_t &tn : term_names) {
		prog_constr += tn + to_string_t(", ");
	}
	prog_constr += to_string_t("}, ");
	if(rr.is_fact() || rr.is_goal()) {
		prog_constr += to_string_t("std::vector<raw_term> {}");
	} else {
		prog_constr += prft_name;
	}
	prog_constr += to_string_t(");\n");
	return rule_name;
}

// Generate the C++ code to generate the given TML lexeme

string_t driver::generate_cpp(const lexeme &lex) {
	return to_string_t("STR_TO_LEXEME(") + lexeme2str(lex) + to_string_t(")");
}

// Generate the C++ code to generate the given TML directive

string_t driver::generate_cpp(const directive &dir, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name, map<elem, string_t> &elem_cache) {
	string_t dir_name = to_string_t("dir") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("directive ") + dir_name + to_string_t(";\n");
	switch(dir.type) {
		case directive::STR:
			prog_constr += dir_name + to_string_t(".type = directive::STR;\n");
			prog_constr += dir_name + to_string_t(".rel = ") +
				generate_cpp(dir.rel, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".arg = ") + generate_cpp(dir.arg) +
				to_string_t(";\n");
			break;
		case directive::FNAME:
			prog_constr += dir_name + to_string_t(".type = directive::FNAME;\n");
			prog_constr += dir_name + to_string_t(".rel = ") +
				generate_cpp(dir.rel, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".arg = ") + generate_cpp(dir.arg) +
				to_string_t(";\n");
			break;
		case directive::CMDLINE:
			prog_constr += dir_name + to_string_t(".type = directive::CMDLINE;\n");
			prog_constr += dir_name + to_string_t(".rel = ") +
				generate_cpp(dir.rel, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".n = ") +
				to_string_t(to_string(dir.n).c_str()) + to_string_t(";\n");
			break;
		case directive::STDIN:
			prog_constr += dir_name + to_string_t(".type = directive::STDIN;\n");
			prog_constr += dir_name + to_string_t(".rel = ") +
				generate_cpp(dir.rel, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			break;
		case directive::STDOUT:
			prog_constr += dir_name + to_string_t(".type = directive::STDOUT;\n");
			prog_constr += dir_name + to_string_t(".t = ") +
				generate_cpp(dir.t, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			break;
		case directive::TREE:
			prog_constr += dir_name + to_string_t(".type = directive::TREE;\n");
			prog_constr += dir_name + to_string_t(".t = ") +
				generate_cpp(dir.t, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			break;
		case directive::TRACE:
			prog_constr += dir_name + to_string_t(".type = directive::TRACE;\n");
			prog_constr += dir_name + to_string_t(".rel = ") +
				generate_cpp(dir.rel, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			break;
		case directive::BWD:
			prog_constr += dir_name + to_string_t(".type = directive::BWD;\n");
			break;
		case directive::EVAL:
			prog_constr += dir_name + to_string_t(".type = directive::EVAL;\n");
			prog_constr += dir_name + to_string_t(".eval_sym = ") +
				generate_cpp(dir.eval_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".domain_sym = ") +
				generate_cpp(dir.domain_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".quote_sym = ") +
				generate_cpp(dir.quote_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".timeout_num = ") +
				to_string_t(to_string(dir.timeout_num.num).c_str()) + to_string_t(";\n");
			break;
		case directive::QUOTE:
			prog_constr += dir_name + to_string_t(".type = directive::QUOTE;\n");
			prog_constr += dir_name + to_string_t(".quote_sym = ") +
				generate_cpp(dir.quote_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".domain_sym = ") +
				generate_cpp(dir.domain_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".quote_str = ") +
				generate_cpp(dir.quote_str, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			break;
		case directive::EDOMAIN:
			prog_constr += dir_name + to_string_t(".type = directive::EDOMAIN;\n");
			prog_constr += dir_name + to_string_t(".domain_sym = ") +
				generate_cpp(dir.domain_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".limit_num = ") +
				to_string_t(to_string(dir.limit_num.num).c_str()) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".arity_num = ") +
				to_string_t(to_string(dir.arity_num.num).c_str()) + to_string_t(";\n");
			break;
		case directive::CODEC:
			prog_constr += dir_name + to_string_t(".type = directive::CODEC;\n");
			prog_constr += dir_name + to_string_t(".codec_sym = ") +
				generate_cpp(dir.codec_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".domain_sym = ") +
				generate_cpp(dir.domain_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".eval_sym = ") +
				generate_cpp(dir.eval_sym, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			prog_constr += dir_name + to_string_t(".arity_num = ") +
				to_string_t(to_string(dir.arity_num.num).c_str()) + to_string_t(";\n");
			break;
		case directive::INTERNAL:
			prog_constr += dir_name + to_string_t(".type = directive::INTERNAL;\n");
			prog_constr += dir_name + to_string_t(".internal_term = ") +
				generate_cpp(dir.internal_term, prog_constr, cid, dict_name, elem_cache) + to_string_t(";\n");
			break;
	}
	return dir_name;
}

// Generate the C++ code to generate the given TML program

string_t driver::generate_cpp(const raw_prog &rp, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache) {
	vector<string_t> directive_names;
	for(const directive &dir: rp.d) {
		directive_names.push_back(generate_cpp(dir, prog_constr, cid, dict_name,
			elem_cache));
	}
	vector<string_t> rule_names;
	for(const raw_rule &rr : rp.r) {
		rule_names.push_back(generate_cpp(rr, prog_constr, cid, dict_name,
			elem_cache));
	}
	string_t prog_name = to_string_t("rp") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("raw_prog ") + prog_name + to_string_t(";\n");
	// Insert the rules we have constructed into the final program
	prog_constr += prog_name + to_string_t(".r.insert(") + prog_name +
		to_string_t(".r.end(), { ");
	for(const string_t &rn : rule_names) {
		prog_constr += rn + to_string_t(", ");
	}
	prog_constr += to_string_t("});\n");
	// Insert the directives we have constructed into the final program
	prog_constr += prog_name + to_string_t(".d.insert(") + prog_name +
		to_string_t(".d.end(), { ");
	for(const string_t &dn : directive_names) {
		prog_constr += dn + to_string_t(", ");
	}
	prog_constr += to_string_t("});\n");
	return prog_name;
}

bool driver::transform(raw_prog& rp, const strs_t& /*strtrees*/) {
	lexeme trel = { 0, 0 };
	directives_load(rp, trel);
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
//	if (opts.enabled("sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
	static set<raw_prog *> transformed_progs;
	if(transformed_progs.find(&rp) == transformed_progs.end()) {
		transformed_progs.insert(&rp);
		DBG(o::dbg() << "Pre-Transformation Program:" << endl << endl << rp << endl;)
		
		if(opts.enabled("safe-check")) {
			if(auto res = is_safe(rp)) {
				ostringstream msg;
				// The program is unsafe so inform the user of the offending rule
				// and variable.
				msg << "The variable " << res->first << " of " << res->second <<
					" is not limited. Try rewriting the rule to make its safety clearer.";
				parse_error(msg.str().c_str());
			}
		}
		
		// If we want proof trees, then we need to transform the productions into
		// rules first since only rules are supported by proof trees.
		if(opts.get_string("proof") != "none") {
			o::dbg() << "Transforming Grammar ..." << endl << endl;
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
			o::dbg() << "Transformed Grammar:" << endl << endl << rp << endl;
		}

		if(opts.enabled("program-gen")) {
			uint_t cid = 0;
			string_t rp_generator;
			map<elem, string_t> elem_cache;
			o::dbg() << "Generating Program Generator ..." << endl << endl;
			generate_cpp(rp, rp_generator, cid, to_string_t("d"), elem_cache);
			o::dbg() << "Program Generator:" << endl << endl
				<< to_string(rp_generator) << endl;
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
		if(opts.enabled("cqnc-subsume") || opts.enabled("cqc-subsume") ||
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
					o::dbg() << "CQNC Subsumed Program:" << endl << endl << rp
						<< endl;
				}
				if(opts.enabled("cqc-subsume")) {
					o::dbg() << "Subsuming using CQC test ..." << endl << endl;
					subsume_queries(rp,
						[this](const raw_rule &rr1, const raw_rule &rr2)
							{return cqc(rr1, rr2);});
					o::dbg() << "CQC Subsumed Program:" << endl << endl << rp
						<< endl;
				}
				if(opts.enabled("cqc-factor")) {
					o::dbg() << "Factoring queries using CQC test ..." << endl
						<< endl;
					factor_rules(rp);
					o::dbg() << "Factorized Program:" << endl << endl << rp
						<< endl;
				}
				if(opts.enabled("split-rules")) {
					// Though this is a binary transformation, rules will become
					// ternary after timing guards are added
					o::dbg() << "Converting rules to unary form ..." << endl
						<< endl;
					transform_bin(rp);
					o::dbg() << "Binary Program:" << endl << endl << rp << endl;
				}
			});
			o::dbg() << "Step Transformed Program:" << endl << endl << rp
				<< endl;
			o::dbg() << "Eliminating dead variables ..." << endl << endl;
			eliminate_dead_variables(rp);
			o::dbg() << "Stripped TML Program:" << endl << endl << rp << endl;
		}
	}
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
	for (auto& np : rp.nps) if (!transform(np, pd.strs)) return false;
	return true;
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled("xsb"))     print_xsb(o::to("xsb"), p);
	if (opts.enabled("swipl"))   print_swipl(o::to("swipl"), p);
	if (opts.enabled("souffle")) print_souffle(o::to("souffle"), p);
}

bool driver::prog_run(raw_prog& p, size_t steps, size_t break_on_step) {
//	pd.clear();
//	DBG(o::out() << "original program:"<<endl<<p;)
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	clock_t start, end;
	size_t step = nsteps();
	raw_prog::last_id = 0; // reset rp id counter;
	measure_time_start();
	if (opts.enabled("guards")) {
		tbl->transform_guards(p);
		if (opts.enabled("transformed")) o::to("transformed")
			<< "# after transform_guards:\n" << p << endl << endl;
	} else if (raw_prog::require_guards)
		return error = true,
			throw_runtime_error("Conditional statements require "
				"-g (-guards) option enabled.");
	bool fp = false;


	if (opts.enabled("bitunv")) {
		typechecker tc(p, true);
		if(tc.tcheck()) {
			tbl->spbu  = make_shared<bit_univ>(tbl->get_dict(),
												opts.get_int("bitorder"));
			raw_prog brawp;
			tbl->spbu.get()->btransform(p, brawp);
			tbl->spbu.get()->ptypenv = p.typenv;
			fp = tbl->run_prog_wstrs(brawp, pd.strs, steps, break_on_step);
		}
	}
	//TODO review nested programs since we are forcing two calls to get_rules
	// one with a program without them.
	else fp = tbl->run_prog_wstrs(p, pd.strs, steps, break_on_step);
	o::ms() << "# elapsed: ";
	measure_time_end();
	if (tbl->error) error = true;
	pd.elapsed_steps = nsteps() - step;
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
	return fp;
}

bool driver::add(input* in) {
	if (!rp.parse(in, tbl->get_dict())) return !(error = true);
	transform(rp.p, pd.strs);
	return true;
}

template <typename T>
void driver::list(std::basic_ostream<T>& os, size_t /*n*/) {
	os << rp.p << endl;
}
template void driver::list(std::basic_ostream<char>&, size_t);
template void driver::list(std::basic_ostream<wchar_t>&, size_t);

void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::run(size_t steps, size_t break_on_step) {
	if (!running) restart();
	if (nsteps() == pd.start_step) {
		//transform(rp.p, pd.strs);
		//for (const string& s : str_bltins)
		//	rp.p.builtins.insert(get_lexeme(s));
		output_pl(rp.p);
	}
	if (opts.disabled("run") && opts.disabled("repl")) return true;
	bool fp = prog_run(rp.p, steps, break_on_step);
	if (fp) result = true;
	return fp;
}

bool driver::step(size_t steps, size_t break_on_step) {
	return run(steps, break_on_step);
}

template <typename T>
void driver::info(std::basic_ostream<T>& os) {
	os<<"# step:      \t" << nsteps() <<" - " << pd.start_step <<" = "
		<< (nsteps() - pd.start_step) << " ("
		<< (running ? "" : "not ") << "running)" << endl;
	bdd::stats(os<<"# bdds:     \t")<<endl;
	//DBG(os<<"# opts:    \t" << opts << endl;)
}
template void driver::info(std::basic_ostream<char>&);
template void driver::info(std::basic_ostream<wchar_t>&);

size_t driver::size() {
	return archive::size(*this);
}

void driver::db_load(std::string filename) {
	load_archives.emplace_back(archive::type::BDD, filename, 0, false);
	load_archives.back() >> *this;
}

void driver::db_save(std::string filename) {
	archive ar(archive::type::BDD, filename, archive::size(*this), true);
	ar << *this;
}

void driver::load(std::string filename) {
	if (!ii->size()) {
		load_archives.emplace_back(archive::type::DRIVER, filename,0,0);
		if (!load_archives.back().error) load_archives.back() >> *this;
		return;
	}
	error = true;
	throw_runtime_error(
		"Loading into a running program is not yet supported."); // TODO
}

void driver::save(std::string filename) {
	archive ar(archive::type::DRIVER, filename, archive::size(*this), true);
	ar << *this;
}

void driver::read_inputs() {
	//COUT << "read_inputs() current_input: " << current_input << " next_input: " << (current_input ? current_input->next() : 0) << endl;
	while (current_input && current_input->next()) {
		current_input = current_input->next();
		if (!add(current_input)) return;
		++current_input_id;
		//COUT << "current_inputid: " << current_input_id << endl;
	}
}

driver::driver(string s, const options &o) : rp(), opts(o) {

	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());
	dict.set_bitunv(opts.enabled("bitunv"));
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
	to.bitunv			 = opts.enabled("bitunv");
	to.bitorder          = opts.get_int("bitorder");

	//dict belongs to driver and is referenced by ir_builder and tables
	ir = new ir_builder(dict, to);
	tbl = new tables(dict, to, ir);
	ir->dynenv = tbl;
	ir->printer = tbl; //by now leaving printer component in tables, to be rafactored

	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	tbl->add_print_updates_states(opts.pu_states);
	set_populate_tml_update(opts.enabled("tml_update"));
	set_regex_level(opts.get_int("regex-level"));

	current_input = ii->first();
	if (current_input && !add(current_input)) return;
	read_inputs();
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
	for (auto x : strs_allocated) free((char *)x);
}
