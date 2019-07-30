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

using namespace std;

map<int_t, int_t> tables::varbdd_to_subs(const alt* a, cr_spbdd_handle v)
	const {
	map<int_t, int_t> r;
	decompress(v, 0, [this, a, &r](const term& x) {
		for (auto z : a->inv)
			if (!r.emplace(z.second, x[z.first]).second)
				throw 0;
	}, a->varslen);
	return r;
}

struct proof_dag {
	struct vertex {
		size_t step;
		term t;
		vertex(const term& t, size_t step) : step(step), t(t) {}
		bool operator<(const vertex& v) const {
			if (step != v.step) return step < v.step;
			return t < v.t;
		}
	};
	map<vertex, set<vertex>> E;
	void add(const term& h, const vector<term>& b, size_t step) {
		set<vertex> s;
		for (const term& t : b) s.emplace(t, step - 1);
		E.emplace(vertex(h, step), move(s));
	}
};

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
