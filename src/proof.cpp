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

using namespace std;

vector<map<int_t, int_t>> tables::varbdd_to_subs(const alt* a, cr_spbdd_handle v)
	const {
	vector<map<int_t, int_t>> r;
	decompress(v, 0, [this, a, &r](const term& x) {
		map<int_t, int_t> m;
		for (auto z : a->inv)
			if (!m.emplace(z.second, x[z.first]).second)
				throw 0;
		r.emplace_back(move(m));
	}, a->varslen);
	return r;
}

void subs_to_rule(const rule& r, const alt* a, term& h, vector<term>& b,
	const map<int, int>& e) {
	h = r.t, b = a->t;
	for (int_t& i : h) if (i < 0) i = e.at(i);
	for (term& t : b) for (int_t& i : t) if (i < 0) i = e.at(i);
}

bool proof_dag::vertex::operator<(const vertex& v) const {
	if (step != v.step) return step < v.step;
	return t < v.t;
}

void proof_dag::add(const term& h, const vector<term>& b, size_t step) {
	set<vertex> s;
	for (const term& t : b) s.emplace(t, step - 1);
	vertex v = vertex(h, step);
	E[v].insert(move(s)), L[step].insert(v);
}

void tables::print_proof(std::wostream& os, const proof_dag& pd) const {
	for (const auto& x : pd.L) {
		for (const proof_dag::vertex& v : x.second)
			for (const set<proof_dag::vertex>& s : pd.E.at(v)) {
				os << to_raw_term(v.t) << L" :- ";
				for (const proof_dag::vertex& t : s)
					os << to_raw_term(t.t) << ' ';
				os << endl;
			}
		}
}

/*std::wostream operator<<(std::wostream& os, const proof_dag::vertex& v) {
	return os << v.step << to_raw_term(v.t);
}*/

proof_dag tables::get_proof() const {
	size_t n = levels.size();
	proof_dag pd;
	map<size_t, spbdd_handle>::const_iterator it;
	term h;
	vector<term> b;
	map<int_t, int_t> e;
	while (--n)
		for (const rule& r : rules)
			for (const alt* a : r)
				if ((it=a->levels.find(n)) != a->levels.end())
					for (	const map<int_t, int_t>& e :
						varbdd_to_subs(a, it->second))
						subs_to_rule(r, a, h, b, e),
						pd.add(h, b, n);
	print_proof(wcerr, pd);
	return pd;
}

/*void tables::bwd_facts(const vector<level>& v, proof_dag& p) {
	size_t l = v.size();
	spbdd_handle x, y;
	bool b;
	while (--l) {
		for (const rule& r : rules) {
			if ((x = v[l][r.t.tab] && r.h) == bdd_handle::F)
				continue;
			b = false;
			for (const alt* a : r) {
				bdd_handles z;
				for (const body* b : *a) {
					y = v[l - 1][b->tab] && b->q;
					if (b |= y == bdd_handle::F) break;
					z.push_back(y);
				}
				if (b) break;
				add_witnesses(x, z, p, l)
			}
		}
	}
}
*/
