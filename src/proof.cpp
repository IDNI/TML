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
		map<size_t, spbdd_handle>::const_iterator it;
		it = a->levels.find(level);
		if (it == a->levels.end()) continue;
		spbdd_handle t = it->second && h;
		if (t == bdd_handle::F) continue;
		if (level) {
			auto it = a->levels.find(level - 1);
			if (it != a->levels.end()) t = t % it->second;
		}
		for (const env& e : varbdd_to_subs(a, t))
			f(rl, level, n, move(subs_to_rule(rules[rl], a, e)));
	}
}

void tables::term_get_grounds(const term& t, size_t level, cb_ground f) {
	spbdd_handle h = from_fact(t);
	for (size_t r : ts[t.tab].r)
		if (rules[r].neg == t.neg)
			rule_get_grounds(h, r, level, f);
}

set<tables::witness> tables::get_witnesses(const term& t, size_t l) {
	set<witness> r;
	term_get_grounds(t, l, [&r](size_t rl, size_t, size_t al,
		const vector<term>& b) { r.emplace(rl, al, b); });
	return r;
}

size_t tables::get_proof(const term& q, proof& p, size_t level) {
	set<witness> s;
	proof_elem e;
	DBG(wcout<<L"current p: " << endl; print(wcout, p);)
	DBG(wcout<<L"proving " << to_raw_term(q) << L" level " << level<<endl;)
	while ((s = get_witnesses(q, level)).empty())
		if (!level--)
			return 0;
	bool f;
	for (const witness& w : s) {
		DBG(wcout<<L"witness: "; print(wcout, w); wcout << endl;)
		e.rl = w.rl, e.al = w.al, e.b.clear(), e.b.reserve(w.b.size()); 
		for (const term& t : w.b) {
			f = false;
			for (size_t n = 0; n != level; ++n)
				if (p[n].find(t) != p[n].end()) {
					f = true;
					break;
				}
			if (!f) e.b.emplace_back(get_proof(t, p, level - 1), t);
		}
		p[level][q].insert(e);
	}
	return level;
}

void tables::get_goals() {
	proof p(levels.size());
	set<term> s;
	for (const term& t : goals)
		decompress(ts[t.tab].t && from_fact(t), t.tab,
			[&s](const term& t) { s.insert(t); }, t.size());
	for (const term& g : s) get_proof(g, p, levels.size() - 1);
	print(wcout, p);
}
