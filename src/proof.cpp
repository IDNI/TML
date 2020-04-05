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

vector<env> tables::varbdd_to_subs(const alt* a, cr_spbdd_handle v)
	const {
	vector<env> r;
	decompress(v, 0, [a, &r](const term& x) {
		env m;
		for (auto z : a->inv)
			if (!m.emplace(z.second, x[z.first]).second)
				throw 0;
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
	// D: addtail needs a bitsmeta, one tbl.bm, another alt.bm (or custom?)
	table& tbl = tbls[rules[rl].tab];
	for (size_t n = 0; n != rules[rl].size(); ++n)
		if (a = rules[rl][n], has(a->levels, level))
			for (const env& e : varbdd_to_subs(a,
				addtail(h, rules[rl].t.size(), a->varslen, tbl.bm, a->bm)))
				f(rl, level, n, move(subs_to_body(a, e)));
}

void tables::term_get_grounds(const term& t, size_t level, cb_ground f) {
	spbdd_handle h = from_fact(t), x;
	if (!level) f(-1, 0, -1, {t});
	if (level > 1) {
		spbdd_handle	x = levels[level-1][t.tab] && h,
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
//		DBG(o::out()<<L"witness: "; print(o::out(), w); o::out()<<endl;)
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

size_t tables::get_proof(const term& q, proof& p, size_t level, size_t dep) {
	set<witness> s;
	proof_elem e;
	if (!level) return 0;
	if (!--dep) return -1;
//	DBG(o::out()<<L"current p: " << endl; print(o::out(), p);)
//	DBG(o::out()<<L"proving " << to_raw_term(q) << L" level "<<level<<endl;)
	while ((s = get_witnesses(q, level)).empty())
		if (!level--)
			return 0;
	bool f;
	for (const witness& w : s) {
//		DBG(o::out()<<L"witness: "; print(o::out(), w); o::out()<<endl;)
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
			e.b.emplace_back(level?get_proof(t,p,level-1,dep):0, t);
		}
		p[level][q].insert(e);
	}
	return level;
}

bool tables::get_goals(wostream& os) {
	proof p(levels.size());
	set<term> s;
	for (const term& t : goals)
		decompress(tbls[t.tab].tq && from_fact(t), t.tab,
			[&s](const term& t) { s.insert(t); }, t.size());
	for (const term& g : s)
		if (bproof) get_proof(g, p, levels.size() - 1);
		else os << to_raw_term(g) << L'.' << endl;
	if (bproof) print(os, p);
	return goals.size() || bproof;
}
