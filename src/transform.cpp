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
#include <cstring>
#include "driver.h"
#include "err.h"
using namespace std;

#define get_var_elem(i) elem(elem::VAR, dict.get_var_lexeme(i))

void driver::refresh_vars(raw_term& t, size_t& v, map<elem, elem>& m) {
	for (elem& e : t.e)
		if (e.type == elem::VAR && m.find(e) == m.end())
			m.emplace(e, elem(elem::VAR, e.e));
	for (elem& e : t.e) if (e.type == elem::VAR) e = m[e];
}

raw_rule driver::refresh_vars(raw_term h, vector<vector<raw_term>> b) {
	raw_rule r;
	size_t v = 1;
	map<elem, elem> m;
	r.h.emplace_back(), refresh_vars(r.h[0] = h, v, m);
	for (vector<raw_term> a : b) {
		r.b.emplace_back();
		for (raw_term t : a)
			refresh_vars(t, v, m), r.b.back().push_back(t);
	}
	return r;
}

set<raw_rule> driver::refresh_vars(raw_rule& r) {
	set<raw_rule> s;
	for (raw_term h : r.h) {
		raw_rule t = refresh_vars(h, r.b);
		t.type = r.type;
		s.insert(t);
	}
	return s;
}

raw_term driver::from_grammar_elem(const elem& v, int_t v1, int_t v2) {
	return raw_term({v, elem_openp, get_var_elem(v1), get_var_elem(v2), elem_closep});
}

raw_term driver::from_grammar_elem_nt(const lexeme& r, const elem& c,
	int_t v1, int_t v2) {
	raw_term t;
	t.e.emplace_back(elem::SYM, r),
	t.e.emplace_back(elem_openp),
	t.e.emplace_back(get_var_elem(v1)),
	t.e.emplace_back(c),
	t.e.emplace_back(get_var_elem(v2)),
	t.e.emplace_back(elem_closep);
	return t.calc_arity(current_input), t;
}

raw_term driver::from_grammar_elem_builtin(const lexeme& r, const string_t& b,
	int_t v){
	return raw_term({ elem(elem::SYM, r),
		elem_openp, elem(elem::SYM, dict.get_lexeme(b)),
		get_var_elem(v), get_var_elem(v+1), elem_closep});
}

#define from_string_lex(rel, lex, n) raw_rule(raw_term({ \
		elem(elem::SYM, rel), \
		elem_openp, \
		elem(elem::SYM, dict.get_lexeme(to_string_t(lex))), \
		elem(n), elem(n+1), \
		elem_closep}))

void driver::transform_string(const string_t& s, raw_prog& r, const lexeme &rel) {
	for (int_t n = 0; n < (int_t)s.size(); ++n) {
		r.r.push_back(raw_rule(raw_term({
			elem(elem::SYM, rel),
			elem_openp, elem(n),
			elem((char32_t) s[n]),
			elem(n+1),
			elem_closep})));
		if (isspace(s[n]))
			r.r.push_back(from_string_lex(rel, "space", n));
		if (isdigit(s[n]))
			r.r.push_back(from_string_lex(rel, "digit", n));
		if (isalpha(s[n]))
			r.r.push_back(from_string_lex(rel, "alpha", n));
		if (isalnum(s[n]))
			r.r.push_back(from_string_lex(rel, "alnum", n));
		if (isprint(s[n]))
			r.r.push_back(from_string_lex(rel, "printable", n));
	}
}

#define append_sym_elem(x, s) (x).push_back(elem(elem::SYM, s))
#define append_openp(x) (x).push_back(elem_openp)
#define append_closep(x) (x).push_back(elem_closep)
#define cat(x, y) x.insert(x.end(), y.begin(), y.end())
#define cat_in_brackets(x, y) \
	append_openp((x).e), cat((x).e, (y).e), append_closep((x).e)
#define cat_relsym_openp(x, r) append_sym_elem((x).e, r), append_openp((x).e)
#define term_close(x) append_closep((x).e), (x).calc_arity()

void elim_nullables(set<production>& s) {
	set<elem> nullables;
loop1:	size_t sz = nullables.size();
	for (const production& p : s) {
		bool null = true;
		if (p.p.size() != 2 || !(p.p[1].e == "null"))
			for (size_t n = 1; null && n != p.p.size(); ++n)
				null &= has(nullables, p.p[n]);
		if (null) nullables.insert(p.p[0]);
	}
	if (sz != nullables.size()) goto loop1;
	set<production> t;
	for (auto p : s)
		if (p.p.size() == 2 && p.p[1].e == "null")
			t.insert(p);
	for (auto x : t) s.erase(x);
	t.clear();
loop2:	sz = s.size();
	for (auto p : s)
		for (size_t n = 1; n != p.p.size(); ++n)
			if (has(nullables, p.p[n])) {
				production q = p;
				q.p.erase(q.p.begin() + n),
				t.insert(q);
//					r.g.push_back(q);
			}
	for (auto x : t) s.insert(x);
	t.clear();
	if (sz != s.size()) goto loop2;
}

//#define BWD_GRAMMAR
//#define ELIM_NULLS

/* Transform all the productions in the given program into pure TML
 * rules. */

void driver::transform_grammar(raw_prog& r, lexeme rel, size_t len) {
	if (r.g.empty()) return;
	static const set<string_t> b = {
		to_string_t("alpha"), to_string_t("alnum"),
		to_string_t("digit"), to_string_t("space"),
		to_string_t("printable") };
	for (size_t k = 0; k != r.g.size();) {
		if (r.g[k].p.size()<2)parse_error(err_empty_prod,r.g[k].p[0].e);
		size_t n = 0;
		while (n<r.g[k].p.size() && r.g[k].p[n].type != elem::ALT) ++n;
		if (n == r.g[k].p.size()) { ++k; continue; }
		r.g.push_back({
			vector<elem>(r.g[k].p.begin(), r.g[k].p.begin() + n) });
		r.g.push_back({
			vector<elem>(r.g[k].p.begin()+n+1, r.g[k].p.end()) });
		r.g.back().p.insert(r.g.back().p.begin(), r.g[k].p[0]);
		r.g.erase(r.g.begin() + k);
	}
	for (production& p : r.g) {
		for (size_t n = 0; n < p.p.size(); ++n)
			if (p.p[n].type == elem::STR) {
				lexeme l = p.p[n].e;
				p.p.erase(p.p.begin() + n);
				bool esc = false;
				for (ccs s = l[0]+1; s != l[1]-1; ++s)
					if (*s == '\\' && !esc) esc=true;
					else p.p.insert(p.p.begin()+n++,
						elem((char32_t) *s)),esc=false;
			}
	}
#ifdef ELIM_NULLS
	set<production> s;
	for (auto x : r.g) s.insert(x);
	elim_nullables(s), r.g.clear(), r.g.reserve(s.size());
	for (auto x : s) r.g.push_back(x);
	s.clear();
#endif
	raw_rule l;
/*	raw_term m;
	m = fro_grammar_elem({elem::SYM,0,dict.get_lexeme("null")},1,1);
	l.add_head(m);
	l.add_body(from_grammar_elem_nt(r.d[0].rel.e,
				{elem::VAR,0,get_var_lexeme(2)},1,3));
	r.r.push_back(l), l.clear(), l.add_head(m);
	l.add_body(from_grammar_elem_nt(r.d[0].rel.e,
				{elem::VAR,0,get_var_lexeme(2)},3,1));
	r.r.push_back(l);*/
	for (production& p : r.g) {
		if (p.p.size() < 2) continue;
		l.clear();
		if (p.p.size() == 2 && p.p[1].e == "null") {
#ifndef ELIM_NULLS
			raw_term t = from_grammar_elem(p.p[0], 1, 1);
			l.h.push_back(t);
			elem e = get_var_elem(2);
			l.b.emplace_back();
			l.b.back().push_back(from_grammar_elem_nt(rel,e,1,3));
			r.r.push_back(l), l.clear(), l.h.push_back(t),
			l.b.emplace_back(),
			l.b.back().push_back(from_grammar_elem_nt(rel,e,3,1));
#endif
//			_r.r.push_back({{t, t}});
//			_r.r.back().b[0].neg = true;
		} else {
//			o::out() << p << endl;
			size_t v = p.p.size();
			l.h.push_back(from_grammar_elem(p.p[0], 1, p.p.size()));
			l.b.emplace_back();
			for (size_t n = 1; n < p.p.size(); ++n) {
				if (p.p[n].type == elem::CHR) {
					l.b.back().push_back(from_grammar_elem_nt(
						rel, p.p[n], n, n+1));
					continue;
				}
				string_t str = lexeme2str(p.p[n].e);
				if (has(b, str))
					l.b.back().push_back(
						from_grammar_elem_builtin(
							rel, str,n)), ++v;
				else l.b.back().push_back(
					from_grammar_elem(p.p[n],n,n+1));
			}
		}
		r.r.push_back(l);
	}
	raw_term t;
	append_sym_elem(t.e, dict.get_lexeme("start")), append_openp(t.e),
	t.e.push_back(elem((int_t)0)), t.e.push_back(elem((int_t)len)),
	append_closep(t.e), t.calc_arity(current_input);
	raw_rule rr;
	rr.type = raw_rule::GOAL, rr.h = {t}, r.r.push_back(rr);
	DBG(o::out() << "transformed grammar:" << endl << r;)
}

typedef pair<raw_term, vector<raw_term>> frule;

/*!
 * Convert a raw program into a flat one.
 * 
 * Convert a raw program to a flat one, i.e. for each rule of the original raw
 * program, if the type is not a goal or none, refresh the vars and add it back
 * again to the program.
 */
struct flat_rules : public vector<frule> {
	raw_term q;
	map<pair<elem, ints>, set<size_t>> m;

	flat_rules(const raw_prog& p, driver& d) {
		for (const raw_rule& r : p.r)
			if (r.type == raw_rule::GOAL) q = r.h[0]; // FIXME
			else if (r.type != raw_rule::NONE) continue;
			else for (raw_term h : r.h)
				for (vector<raw_term> a : r.b) {
					size_t v = 1;
					map<elem, elem> m1;
					d.refresh_vars(h, v, m1);
					for (raw_term& b : a)
						d.refresh_vars(b, v, m1);
					emplace_back(h, a),
					m[{h.e[0],h.arity}].insert(size());
				}
		if (!q.e.empty()) insert(begin(), {q, {}});
	}
};

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const flat_rules& f) {
	for (auto x : f) os << raw_rule(x.first, x.second) << endl;
	return os;
}

void driver::transform_state_blocks(raw_prog &rp, set<lexeme> guards) {
	for (raw_prog& nrp : rp.nps) transform_state_blocks(nrp, guards);
	for (state_block& sb : rp.sbs) {
		set<lexeme> grds(guards);
		grds.insert(sb.label);
		transform_state_blocks(sb.p, grds);
		raw_term rt(elem(elem::SYM, sb.label), vector<elem>{});
		if (sb.flip) {
			raw_term h(rt); h.neg = true;
			rp.r.push_back(raw_rule(h, rt));
		}
		for (raw_rule& r : sb.p.r) {
			raw_term rt(elem(elem::SYM, sb.label), vector<elem>{});
			if (r.prft) r.prft = raw_form_tree(elem::AND,
				make_shared<raw_form_tree>(rt),
				make_shared<raw_form_tree>(*r.prft));
			else {
				if (r.b.empty()) r.b.emplace_back();
				for (auto& b : r.b) b.push_back(rt);
			}
			rp.r.push_back(move(r));
		}
	}
	rp.sbs.clear();
}
