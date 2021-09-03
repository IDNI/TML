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

/* Get the proofs of the given term occuring at the given level stemming
 * directly from a DNF rule head. Do this by querying the corresponding
 * instrumentation facts. They will tell us which rules derived the given fact
 * and under which instantiation of the existential quantifiers they were
 * derived. Note that the instrumented fact may correspond to this fact derived
 * at a different level, so we do need to check that the facts that it suggests
 * exist do actually exist at the previous level. Otherwise that proof must be
 * discarded. */

bool tables::get_dnf_proofs(const term& q, proof& p, size_t level, set<pair<term, size_t>> &absent) {
	// Indicates that there is not a legal variable substitution that would derive
	// q as a head
	bool not_exists_proof_valid = true;
	// A set of negative facts that are enough to prevent q from being derived.
	// Evidence for a negative fact.
	proof_elem not_exists_proof;
	not_exists_proof.rl = not_exists_proof.al = 0;
	// Check if the table of the given fact has an instrumentation table
	for(const auto &[instr_tab, orig_rule_neg] : tbls[q.tab].instr_tabs) {
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
		bool exists_mode = q.neg == orig_rule_neg;
		spbdd_handle var_domain = exists_mode ? levels[level][fact_aug.tab] : htrue;
		decompress(var_domain && from_fact(fact_aug), fact_aug.tab,
				[&](const term& t) {
			// Ensure that the current variable instantiations are legal. Needed for
			// proving negative facts by showing that no variable instantiation would
			// satisfy rules of a relation.
			for(const int_t &el : t) {
				// Use the type bits to determine what the value limits should be
				if(((el & 3) == 1 && (el >> 2) >= ir_handler->chars) ||
					((el & 3) == 2 && (el >> 2) > ir_handler->nums) ||
					((el & 3) == 0 && (el >> 2) >= ir_handler->syms) ||
					(el & 3) == 3) return;
			}
			// Find the single rule corresponding to this instrumentation table
			for(int_t rule_idx = 0; rule_idx < rules.size(); rule_idx++) {
				const rule &rul = rules[rule_idx];
				if(rul.tab != fact_aug.tab) continue;
				// By construction, each instrumentation relation has only one rule
				assert(rul.size() == 1);
				const alt* const &alte = rul[0];
				// Now we want to map the variables of the instrumentation rule to
				// their substitutions
				map<int_t, int_t> subs;
				for(int_t i = 0; i < t.size(); i++) {
					subs[rul.t[i]] = t[i];
				}
				// Now we want to substitute the variable instantiations into the
				// rule body. If all these body terms were true, then we have enough to
				// prove the fact q.
				proof_elem exists_proof;
				exists_proof.rl = rule_idx;
				exists_proof.al = 0;
				for(term body_tm : alte->t) {
					for(int_t &arg : body_tm) {
						auto var_sub = subs.find(arg);
						// Replace argument with substitution if present
						if(var_sub != subs.end()) arg = var_sub->second;
					}
					exists_proof.b.push_back({level-1, body_tm});
				}
				// Now to prove that the a positive fact q is true, we want to prove
				// that all the body terms are true using the levels structure. If we
				// cannot prove them, then the truth proof under construction must be
				// discarded. And to be able to prove a negative fact true, we want to
				// show that the negation of a body term is true.
				
				// Indicates whether all body terms are true 
				bool exists_proof_valid = true;
				for(auto &[body_level, body_tm] : exists_proof.b) {
					term negated_body_tm = body_tm;
					negated_body_tm.neg = !negated_body_tm.neg;
					// If we are trying to prove a positive fact, then we need a proof of
					// each body term. If we are trying to prove a negative fact, we need
					// a proof of a negation of a body term.
					if(get_proof(exists_mode ? body_tm : negated_body_tm, p, body_level, absent) != exists_mode) {
						// If q head positive, then a body proof failed. So there cannot
						// exist an instantitation of variables in current rule to make head
						// q.
						exists_proof_valid = false;
						// If q head negative, then we have just found a proof that this
						// variable instantiation cannot work.
						if(!exists_mode) {
							pair<nlevel, term> counter_example = {level-1, negated_body_tm};
							// Avoid duplicating counter-examples.
							if(find(not_exists_proof.b.begin(), not_exists_proof.b.end(), counter_example) == not_exists_proof.b.end()) {
								not_exists_proof.b.push_back(counter_example);
							}
						}
						break;
					}
				}
				if(exists_proof_valid) {
					// The presence of an instantiation is incompatible with the lack of
					// existence of one.
					not_exists_proof_valid = false;
					if(exists_mode) {
						// Add this proof as one of the many possible proving this positive
						// fact
						p[level][q].insert(exists_proof);
					}
				}
			}
		}, fact_aug.size());
	}
	// Now that we have gone through all the rules of the given relation, we are
	// in a position to fully determine the lack of existence of a variable
	// instantiation that would derive the positive head.
	if(not_exists_proof_valid) {
		set<proof_elem> augmented_witnesses;
		for(proof_elem witnes : p[level][q]) {
			witnes.b.insert(witnes.b.end(), not_exists_proof.b.begin(), not_exists_proof.b.end());
			augmented_witnesses.insert(witnes);
		}
		p[level][q] = augmented_witnesses;
	}
	return p[level].find(q) != p[level].end();
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
	if(q.neg == qsat) { return false; }
	// The proof for this fact may stem from a DNF rule's derivation. There may be
	// a multiplicity of these proofs. Get them.
	if(level > 0) get_dnf_proofs(q, p, level, absent);
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
