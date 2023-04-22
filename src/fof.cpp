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

#include "fof.h"
#include <algorithm>
#include <cassert>
#include <iostream>

using namespace std;

ir_builder *builder;

ostream& operator<<(ostream& os, const term& t) {
	if (t.empty() && t.tab == -1) return os << "<empty term>";
	if (t.neg) os << "~";
	if (t.size() != 0) os << t.tab << '(';
	else os << t.tab;
	for (size_t n = 0; n != t.size(); ++n) {
		os << builder->get_elem(t[n]);
		if (n == t.size() - 1) os << ')'; else os << ' ';
	}
	return os;
}

ostream& operator<<(ostream& os, const clause& c) {
	size_t n = 0;
	for (const term& t : c) if (os << t; ++n != c.size()) os << ", ";
	return os;
}

ostream& operator<<(ostream& os, const dnf& d) {
	size_t n = 0;
	for (const clause& c : d) if (os << c; ++n != d.size()) os << "; ";
	return os;
}

ostream& operator<<(ostream& os, const prog& p) {
	for (size_t n = 0; n != p.size(); ++n)
		os << '{' << endl << p.at(n).first << " :- " <<
			p.at(n).second << '.' << endl << '}' << endl;
	return os;
}

//---------------------------------------------------------

clause simplify(const clause& c) {
	for (term t : c)
		if (t.neg = !t.neg; c.find(t) != c.end())
			return {};
	return c;
}

bool operator<=(const clause& x, const clause& y) {
	for (const term& t : x)
		if (y.find(t) == y.end()) return false;
	return true;
}

dnf simplify(const dnf& x) {
	dnf y, z;
	for (clause c : x)
		if (!(c = simplify(c)).empty()) y.insert(c);
	for (clause c : y) {
		bool f = false;
		for (clause d : y)
			if (c != d && c <= d) { f = true; break; }
		if (!f) z.insert(c);
	}
	return z;
}

void simplify(prog& p) { for (auto& x : p) x.second = simplify(x.second); }

//-----------------------------------------------------------------------------

dnf operator||(const dnf& x, const dnf& y) {
	dnf r;
	return r.insert(x.begin(), x.end()), r.insert(y.begin(), y.end()), r;
}

clause operator&&(const clause& x, const clause& y) {
	clause r = x;
	return r.insert(y.begin(), y.end()), simplify(r);
}

dnf operator&&(const dnf& x, const clause& y) {
	dnf r;
	for (const clause& c : x) r.insert(c && y);
	return r;
}

dnf operator&&(const dnf& x, const dnf& y) {
	dnf r;
	for (const clause& c : x) for (const clause& d : (y && c)) r.insert(d);
	return simplify(r);
}

//-----------------------------------------------------------------------------

term operator~(const term& x) {
	term r(x);
	return r.neg = !x.neg, r;
}

dnf operator~(const clause& x) {
	dnf r;
	for (const term& t : x) r.insert({~t});
	return r;
}

dnf operator~(const dnf& x) {
	dnf r;
	for (const clause& c : x) r = r || ~c;
	return r;
}

rel get_tmprel() {
	static int_t last = (1 << 16);
	return ++last;
}

term mkterm(int_t rel, const set<int_t>& v) {
	term r;
	r.insert(r.end(), v.begin(), v.end());
	r.tab = rel;
	return r;
}

void get_vars(const term& t, set<int_t>& r) {
	for (int_t i : t) if (i < 0) r.insert(i);
}

set<int_t> get_vars(const dnf& x) {
	set<int_t> r;
	for (const clause& c : x) for (const term& t : c) get_vars(t, r);
	return r;
}

term get_head(const dnf& d, const set<int_t>& q) {
	set<int_t> v = get_vars(d), r;
	for (int_t i : v) if (q.find(i) == q.end()) r.insert(i);
	return mkterm(get_tmprel(), r);
}

dnf& top(prog& p) {
	return p.back().second;
}

const dnf& top(const prog& p) {
	return p.back().second;
}

prog from_term(const term& t) { return {{{}, {{t}}}}; }

prog operator&&(const prog& x, const prog& y) {
	assert(!x.empty() && !y.empty());
	prog r;
	for (size_t n = 0; n != x.size() - 1; ++n) r.push_back(x[n]);
	for (size_t n = 0; n != y.size() - 1; ++n) r.push_back(y[n]);
	return r.emplace_back(term{}, top(x) && top(y)), r;
}

prog operator||(const prog& x, const prog& y) {
	assert(!x.empty() && !y.empty());
	prog r;
	for (size_t n = 0; n != x.size() - 1; ++n) r.push_back(x[n]);
	for (size_t n = 0; n != y.size() - 1; ++n) r.push_back(y[n]);
	r.emplace_back(term{}, top(x) || top(y));
	return r;
}

prog operator~(const prog& x) {
	prog r = x;
	return (top(r) = ~top(r)), r;
}

prog all(const prog& p, int_t v, int_t t) { return ~ex(~p, v, t); }

prog ex(const prog& p, int_t v, int_t ) {
	prog r = p;
	r.back() = { get_head(top(p), {v}), top(p) };
	r.push_back({{}, {{r.back().first}}});
	return simplify(r), r;
}

ostream& operator<<(ostream& os, const set<pair<clause, dnf>>& p) {
	for (auto& x : p)
		if (x.second.size())
			os << x.first << " :- " << x.second << '.' << endl;
		else os << x.first << '.' << endl;
	return os;
}

f_prog unseq(const prog& p) {
	dnf d;
	set<pair<clause, dnf>> r;

	vector<term> t;
	for (size_t n = 0; n != p.size(); ++n) {
		t.push_back(mkterm(get_tmprel(),{}));
		term aux0 = t.back(); aux0.neg = true;
		r.emplace(clause{p[n].first, {aux0}}, p[n].second && dnf{{{t.back()}}});

	}
	for (size_t n = 0; n != p.size() - 1; ++n)
		r.emplace(clause{{t[n + 1]}}, dnf{{{t[n]}}});
	r.emplace(clause{{t[0]}}, dnf{});
	return r;
}

void fof_init_tables(vector<term> &v) {
	for (auto &t : v) {
		ints ts {(int_t) t.size()};
		int_t tab = builder->get_table(builder->get_sig(t.tab, ts));
		if (t.tab > (1 << 16)) {
			assert(tab != t.tab && "FOF: error encoding tmp tables");
			builder->set_hidden_table(tab);
			t.tab = tab;
		}
	}
}

void to_flat_prog(term &t, ir_builder *irb, const prog &p, flat_prog &m) {
	builder = irb;
	f_prog fp = unseq(p);
	cout << "FOF unseq prog:" << endl;
	cout << fp << endl;

	vector<term> v;
	term h;
	for (auto &r : fp) {
		for (auto &hr : r.first) {
			if (hr.tab == -1) //emtpy_term
				h = t;
			else h = hr;

			if (r.second.size() == 0) {
				v.push_back(h);
				fof_init_tables(v);
				m.insert(v);
				v.clear();
			}
			else
				for (auto &d : r.second) {
					v.push_back(h);
					v.insert(v.end(), d.begin(), d.end());
					fof_init_tables(v);
					m.insert(v);
					v.clear();
				}
		}
	}
}

void print_fof(prog& p, ir_builder *irb) {
	builder = irb;
	cout << "FOF transformed fol to prog:" << endl;
	cout << p << endl;
}
