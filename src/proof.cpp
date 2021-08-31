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
#include "tables.h"
#include "input.h"
#include "output.h"

using namespace std;

/* The carry proof of a term is the one that is implied by its existence in the
 * previous step. This is as opposed to an explicit derivation by a DNF rule at
 * the current step. Add the corresponding proof witness if it was there. Return
 * false if the fact is not actually there in the previous step. */

bool tables::get_carry_proof(const term& q, proof& p, size_t level, set<pair<term, size_t>> &absent) {
	// If the fact is positive and the current level is not the first, then there
	// is a chance that this fact is carried from the previous level
	if(level > 0 && !q.neg) {
		// Check if the current fact was there in the previous level
		int_t q_prev_sat = (levels[level-1][q.tab] && from_fact(q)) != hfalse;
		// If the fact was there in the previous level, then that is proof enough of
		// the current fact's presence
		if(q_prev_sat) {
			// Prove the previous fact's existence
			get_proof(q, p, level-1, absent);
			// Record this current proof
			proof_elem carry_proof;
			carry_proof.rl = carry_proof.al = 0;
			carry_proof.b = {{level-1, q}};
			p[level][q].insert(carry_proof);
			return true;
		}
	}
	// No carry proof
	return false;
}

/* Get the proofs of the given term occuring at the given level stemming
 * directly from a DNF rule head. Do this by querying the corresponding
 * instrumentation facts. They will tell us which rules derived the given fact
 * and under which instantiation of the existential quantifiers they were
 * derived. Note that the instrumented fact may correspond to this fact derived
 * at a different level, so we do need to check that the facts that it suggests
 * exist do actually exist at the previous level. Otherwise that proof must be
 * discarded. */

bool tables::get_dnf_proofs(const term& q, proof& p, size_t level, set<pair<term, size_t>> &absent) {
	int_t proof_count = 0;
	// Check if the table of the given fact has an instrumentation table
	for(const int_t &instr_tab : q.neg ? set<int_t> {} : tbls[q.tab].instr_tabs) {
		// Convert the fact into an instrumentation fact by switching the table and
		// extending the fact with variables to capture the instrumentation
		term fact_aug = q;
		fact_aug.tab = instr_tab;
		int_t start_var = 0;
		for(const int &elt : fact_aug) start_var = min(start_var, elt);
		for(size_t ext = fact_aug.size(); ext < tbls[fact_aug.tab].len; ext++) {
			fact_aug.push_back(--start_var);
		}
		// Now we capture the instrumented facts that have been derived
		decompress(levels[level][fact_aug.tab] && from_fact(fact_aug), fact_aug.tab,
				[&](const term& t) {
			// Find the single rule corresponding to this instrumentation table
			for(int_t rule_idx = 0; rule_idx < rules.size(); rule_idx++) {
				const rule &rul = rules[rule_idx];
				if(rul.tab != fact_aug.tab) continue;
				assert(rul.size() == 1);
				const alt* const &alte = rul[0];
				// Now we want to map the variables of the instrumentation rule to
				// their substitutions
				map<int_t, int_t> subs;
				for(int_t i = 0; i < t.size(); i++) {
					subs[rul.t[i]] = t[i];
				}
				// Now we want to substitute the variable instantiations into the
				// rule body
				proof_elem body_proof;
				body_proof.rl = rule_idx;
				body_proof.al = 0;
				for(term body_tm : alte->t) {
					for(int_t &arg : body_tm) {
						auto var_sub = subs.find(arg);
						// Replace argument with substitution if present
						if(var_sub != subs.end()) arg = var_sub->second;
					}
					body_proof.b.push_back({level-1, body_tm});
				}
				// Now we want to prove that all the body terms are true using the
				// levels structure. If we cannot prove them, then the current proof
				// under construction must be discarded.
				bool proof_valid = true;
				for(auto &[body_level, body_tm] : body_proof.b) {
					proof_valid = proof_valid && get_proof(body_tm, p, body_level, absent);
				}
				if(proof_valid) {
					// Add this proof as one of the many possible proving this fact
					p[level][q].insert(body_proof);
					proof_count++;
				}
			}
		}, fact_aug.size());
	}
	return proof_count;
}

/* Get all the proofs of the given term occuring at the given level and put them
 * into the given proof object. Record the term and level in the absentee set
 * and return false if the given term does not actually occur at the given
 * level. */

bool tables::get_proof(const term& q, proof& p, size_t level, set<pair<term, size_t>> &absent) {
	// Grow the proof object until it can store proof for this level
	for(; p.size() <= level; p.push_back({}));
	// Check if this term has not already been proven at the given level
	if(p[level].find(q) != p[level].end()) return true;
	// Otherwise check if the term has not already been shown absent
	if(auto it = absent.find({q, level}); it != absent.end()) return false;
	// First ensure that this term can actually be proved. That is ensure that it
	// is present or not present in the relevant step database.
	int_t qsat = (levels[level][q.tab] && from_fact(q)) != hfalse;
	// If the fact is negative, then it cannot have and yet is present, then there
	// cannot be a proof. Same if it is positive but yet is not present.
	if(q.neg == qsat) { absent.insert({q, level}); return false; }
	// The proof for this fact may simply be that it carries from the previous
	// step. Get that proof.
	get_carry_proof(q, p, level, absent);
	// The proof for this fact may stem from a DNF rule's derivation. There may be
	// a multiplicity of these proofs. Get them.
	get_dnf_proofs(q, p, level, absent);
	// Here we know that this fact is valid. Make sure that this fact at least has
	// empty witness set to represent self-evidence.
	p[level][q];
	return true;
}

/* Print proof trees for each goal in the program. Do this by doing a backward
 * chain over the levels structure, which contains the entirity of facts
 * derivable by the given program from the given initial database. */

template <typename T> bool tables::get_goals(std::basic_ostream<T>& os) {
	// Fact proofs are stored by level
	proof p(levels.size());
	set<term> s;
	// Record the facts covered by each goal
	for (const term& t : goals)
		decompress(levels[levels.size() - 1][t.tab] && from_fact(t), t.tab,
			[&s](const term& t) { s.insert(t); }, t.size());
	// Auxilliary variable for get_proof
	set<pair<term, size_t>> absent;
	// Get all proofs for each covered fact
	for (const term& g : s)
		if (opts.bproof) get_proof(g, p, levels.size() - 1, absent);
		else os << ir_handler->to_raw_term(g) << '.' << endl;
	// Print proofs
	if (opts.bproof) print(os, p);
	return goals.size() || opts.bproof;
}
template bool tables::get_goals(std::basic_ostream<char>&);
template bool tables::get_goals(std::basic_ostream<wchar_t>&);
