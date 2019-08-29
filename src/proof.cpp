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

vector<env> tables::varbdd_to_subs(const alt* a, cr_spbdd_handle v)
	const {
	vector<env> r;
	decompress(v, 0, [this, a, &r](const term& x) {
		env m;
		for (auto z : a->inv)
			if (!m.emplace(z.second, x[z.first]).second)
				throw 0;
		r.emplace_back(move(m));
	}, a->varslen);
	return r;
}

vector<term> subs_to_rule(const rule& r, const alt* a, const map<int, int>& e) {
	vector<term> hb;
	hb.clear(), hb.reserve(a->size() + 1),
	hb.push_back(r.t), hb.insert(hb.end(), a->t.begin(), a->t.end());
	for (term& t : hb) for (int_t& i : t) if (i < 0) i = e.at(i);
	return hb;
}

void tables::rule_get_grounds(cr_spbdd_handle& h, size_t rl, size_t level,
	cb_ground f) {
	for (size_t n = 0; n != rules[rl].size(); ++n) {
		const alt *a = rules[rl][n];
		spbdd_handle t = a->levels[level] && h;
		if (t == bdd_handle::F) continue;
		if (level) {
			auto it = a->levels.find(level - 1);
			if (it != a->levels.end()) t = t % it->second;
		}
		for (const env& e : varbdd_to_subs(a, t))
			f(rl, level, n, move(subs_to_rule(rules[rl], a, v, e)));
	}
}

void tables::term_get_grounds(const term& t, size_t level, cb_ground f) {
	spbdd_handle h = from_fact(t);
	for (size_t r : ts[t.tab])
		if (rules[r].neg == t.neg)
			rule_get_grounds(t, r, level, f);
}

struct proof {
	struct node {
		term t;
		size_t level, rl, al;
		vector<size_t> v; // indices of nodes in V
		node() {}
		node(const term& t) : t(t) {}
		node(const term& t, const vector<size_t>& v) : t(t), v(v) {}
		void complete(size_t l, size_t r, size_t a) {
			//, const vector<size_t>& _v) {
			level = l, rl = r, al = a;//, v = _v;
		}
	};
	vector<node> V;
	//map<pair<term, size_t>, set<size_t>> M;
	map<term, set<size_t>> M;
	size_t init(const term& t) {
		return	assert(M.find(t) == M.end()), M.emplace(t, {V.size()}),
			V.emplace_back(t), V.size() - 1;
	}
	size_t init(const term& h, const vector<term>& b) {
		vector<size_t> v;
		for (const term& t : b) v.push_back(init(t));
		return init(h, v);
	}
	void complete(const term& t, size_t level, size_t rl, size_t al) {
		M[t].complete(level, rl, al);
	}
	void add(const node& n) {
		M[{n.t, n.level}].insert(V.size()), V.emplace_back(n);
	}
	void add(const term& t, size_t level, size_t rl, size_t al,
		const vector<size_t>& v) { add({t, level, rl, al, v}); }
};

proof tables::get_proof(set<term> G) {
	// goal -> level -> rule+alt -> bodies
	map<term, map<size_t, map<array<size_t, 2>>>, vector<term>> m;
	// term -> its incomplete proof elem
	map<term, size_t> q;
	auto f = [&G, &m](size_t rl, size_t level, size_t al, vector<term> b) {
		term h = b[0];
		b.erase(b.begin()), G.erase(h);
		assert(m[h][level][{rl, al}].empty());
		m[h][level][{rl, al}] = b;
		G.insert(b.begin(), b.end());
	};
	size_t l = levels.size();
	while (l--)
		for (term g : G)
			term_get_grounds(g, l, f);
}

set<proof_elem> tables::term_get_proof(const term& q, size_t level) {
	vector<proof_elem> p;
	map<term, set<size_t>> m;
	auto it = m.end();
	auto f = [this, &p, &m, &it](size_t rl, size_t level,
		const vector<term>& v) {
		it = m.find(v[0]);
		assert(it != m.end());
		assert(it->second.empty();
		it->second.insert(v.begin() + 1, v.end());
	};
	p.emplace_back(q, -1, level + 1);
	m.insert(q, {0});
	for (auto x : m)
		for (size_t y : ts[x.first.tab].r)
			rule_get_grounds(y, level, f);
}
