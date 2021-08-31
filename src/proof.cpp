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

vector<env> tables::varbdd_to_subs(const alt* a, size_t /*rl*/, size_t/*level*/,
	cr_spbdd_handle v) const
{
	vector<env> r;
	decompress(v, 0, [a, &r, this](const term& x) {
		env m;
		bool flag =true;
		for (auto z : a->inv) {
			int_t arg = x[z.first];
			if(! this->dict.is_valid_sym(arg)) 
				{ flag = false; break; }
			if (!m.emplace(z.second, arg).second)
				{ DBGFAIL; }
		}
		if(flag)
		r.emplace_back(move(m));
	}, a->varslen);
	return r;
}

vector<term> subs_to_rule(const rule& r, const alt* a, const map<int, int>& e) {
	static vector<term> hb;
	hb.clear(), hb.reserve(a->size() + 1),
	hb.push_back(r.t), hb.insert(hb.end(), a->t.begin(), a->t.end());
	for (term& t : hb) for (int_t& i : t) if (i < 0) i = e.at(i);
	return hb;
}

vector<term> subs_to_body(const alt* a, const map<int, int>& e) {
	static vector<term> b;
	b = a->t;
	for (term& t : b) for (int_t& i : t) if (i < 0) i = e.at(i);
	return b;
}

void tables::rule_get_grounds(cr_spbdd_handle& h, size_t rl, size_t level,
	cb_ground f) {
	const alt* a;
	for (size_t n = 0; n != rules[rl].size(); ++n)
		if (a = rules[rl][n], has(a->levels, level))
			for (const env& e : varbdd_to_subs(a, rl, level,
				addtail(h, rules[rl].t.size(), a->varslen)))
				f(rl, level, n, move(subs_to_body(a, e)));
}

void tables::term_get_grounds(const term& t, size_t level, cb_ground f) {
	spbdd_handle h = from_fact(t), x;
	if (!level) f(-1, 0, -1, {t});
	if (level > 1) {
		spbdd_handle x = levels[level-1][t.tab] && h,
				y = levels[level][t.tab] && h;
		if (t.neg?(hfalse==x||hfalse!=y):(hfalse!=x||hfalse==y)) return;
	}
	for (size_t r : tbls[t.tab].r)
		if (rules[r].neg == t.neg)
			rule_get_grounds(h, r, level, f);
}

set<tables::witness> tables::get_witnesses(const term& t, size_t l) {
	set<witness> r;
	term_get_grounds(t, l, [&r](size_t rl, size_t, size_t al,
		const vector<term>& b) { r.emplace(rl, al, b); });
	return r;
}

/*void tables::explain(proof_elem& e) const {
	for (size_t n = 0; n != e.b.size(); ++n)
		if (e.b[n].first == -1) {
		}
}

const set<proof_elem>& tables::explain(const term& q, proof& p, size_t level) {
	set<witness> s;
	proof_elem e;
	if (!level) return 0;
	if (auto it = p[level].find(q); it != p.end()) {
		set<proof_elem> x

		for (const proof_elem& e : it->second) {
			for (const auto& b : e.b) if (b.first == -1) x.insert(e);
			if (x.empty()) continue;
			for (const proof_elem& e : x) it->second.erase(e);
		}
		return it->second;
	}
	while ((s = get_witnesses(q, level)).empty()) if (!level--) return 0;
	bool f;
	for (const witness& w : s) {
//		DBG(o::out()<<"witness: "; print(o::out(), w); o::out()<<endl;)
		e.rl = w.rl, e.al = w.al, e.b.clear(), e.b.reserve(w.b.size());
		for (const term& t : w.b) {
			f = false;
			for (size_t n = level; n--;)
				if (p[n].find(t) != p[n].end()) {
					f = true;
					e.b.emplace_back(n, t);
					break;
				}
			if (f) continue;
			e.b.emplace_back(level?get_proof(t,p,level-1,2):0, t);
		}
		p[level][q].insert(e);
	}
	return p[level][q];
}*/

/* The carry proof of a term is the one that is implied by its existence in the
 * previous step. This is as opposed to an explicit derivation by a DNF rule at
 * the current step. Add the corresponding proof witness if it was there. Return
 * false if the fact is not actually there in the previous step. */

bool tables::get_carry_proof(const term& q, proof& p, size_t level) {
	// If the fact is positive and the current level is not the first, then there
	// is a chance that this fact is carried from the previous level
	if(level > 0 && !q.neg) {
		// Check if the current fact was there in the previous level
		int_t q_prev_sat = (levels[level-1][q.tab] && from_fact(q)) != hfalse;
		// If the fact was there in the previous level, then that is proof enough of
		// the current fact's presence
		if(q_prev_sat) {
			// Prove the previous fact's existence
			get_proof(q, p, level-1);
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

bool tables::get_dnf_proofs(const term& q, proof& p, size_t level) {
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
					proof_valid = proof_valid && get_proof(body_tm, p, body_level);
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
 * into the given proof object. Return false if the given term does not actually
 * occur at the given level. */

bool tables::get_proof(const term& q, proof& p, size_t level) {
	// Grow the proof object until it can store proof for this level
	for(; p.size() <= level; p.push_back({}));
	// Check if this term has not already been proven at the given level
	if(p[level].find(q) != p[level].end()) return true;
	// First ensure that this term can actually be proved. That is ensure that it
	// is present or not present in the relevant step database.
	int_t qsat = (levels[level][q.tab] && from_fact(q)) != hfalse;
	// If the fact is negative, then it cannot have and yet is present, then there
	// cannot be a proof. Same if it is positive but yet is not present.
	if(q.neg == qsat) return false;
	// The proof for this fact may simply be that it carries from the previous
	// step. Get that proof.
	get_carry_proof(q, p, level);
	// The proof for this fact may stem from a DNF rule's derivation. There may be
	// a multiplicity of these proofs. Get them.
	get_dnf_proofs(q, p, level);
	// Here we know that this fact is valid. Make sure that this fact at least has
	// empty witness set to represent self-evidence.
	p[level][q];
	return true;
}

template <typename T>
bool tables::get_goals(std::basic_ostream<T>& os) {
	proof p(levels.size());
	set<term> s;
	for (const term& t : goals)
		decompress(tbls[t.tab].t && from_fact(t), t.tab,
			[&s](const term& t) { s.insert(t); }, t.size());
	for (const term& g : s)
		if (opts.bproof) get_proof(g, p, levels.size() - 1);
		else os << ir_handler->to_raw_term(g) << '.' << endl;
	if (opts.bproof) print(os, p);
	return goals.size() || opts.bproof;
}
template bool tables::get_goals(std::basic_ostream<char>&);
template bool tables::get_goals(std::basic_ostream<wchar_t>&);
