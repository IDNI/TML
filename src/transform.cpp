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
#include "driver.h"
#include "err.h"
using namespace std;

/*lexeme driver::get_char_lexeme(wchar_t c) {
	wstring s;
	return dict.get_lexeme(s += c);
}

lexeme driver::get_num_lexeme(int_t n) { return dict.get_lexeme(to_wstring(n));}
*/

lexeme driver::get_lexeme(const wstring& s) {
	cws w = s.c_str();
	auto it = strs_extra.find({w, w + s.size()});
	if (it != strs_extra.end()) return *it;
	wstr r = wcsdup(s.c_str());
	lexeme l = {r, r + s.size()};
	strs_extra.insert(l);
	return l;
}

lexeme driver::get_var_lexeme(int_t i) {
	wstring s = L"?v";
	return get_lexeme(s += to_wstring(i));
}

#define get_var_elem(i) elem(elem::VAR, get_var_lexeme(i))

#ifdef TRANSFORM_BIN_DRIVER
lexeme driver::get_new_var() {
	static size_t last = 1;
//	size_t sz = dict.nvars();
	lexeme l;
//	for (;;)
	while (vars.find(l = get_var_lexeme(last++)) != vars.end());
	return vars.insert(l), l;//, dict.nvars() == sz) return l;
//		else sz = dict.nvars();
}

void driver::refresh_vars(raw_term& t, size_t& v, map<elem, elem>& m) {
	for (elem& e : t.e)
		if (e.type == elem::VAR && m.find(e) == m.end())
			m.emplace(e, get_var_elem(v++));
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
#endif
/*struct lexemecmp {
	bool operator()(const lexeme& x, const lexeme& y) const {
		return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0] :
			(wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
	}
};*/

raw_term driver::from_grammar_elem(const elem& v, int_t v1, int_t v2) {
	return { false, raw_term::REL, {
		v, elem_openp, get_var_elem(v1), get_var_elem(v2), elem_closep}, {2}};
}

raw_term driver::from_grammar_elem_nt(const lexeme& r, const elem& c,
	int_t v1, int_t v2) {
	raw_term t;
	t.e.emplace_back(elem::SYM, r),
	t.e.emplace_back(elem_openp), t.e.emplace_back(elem_openp),
	t.e.emplace_back(elem_openp),
	t.e.emplace_back(get_var_elem(v1)),
	t.e.emplace_back(elem_closep), t.e.emplace_back(elem_closep),
	t.e.emplace_back(elem_openp), t.e.emplace_back(c),
	t.e.emplace_back(elem_closep), t.e.emplace_back(elem_openp),
	t.e.emplace_back(elem_openp),
	t.e.emplace_back(get_var_elem(v2)),
	t.e.emplace_back(elem_closep), t.e.emplace_back(elem_closep),
	t.e.emplace_back(elem_closep);
	return t.calc_arity(), t;
}

raw_term driver::from_grammar_elem_builtin(const lexeme& r, const wstring& b,
	int_t v){
	return { false, raw_term::REL, {
		elem(elem::SYM, r),
		elem_openp, elem(elem::SYM, get_lexeme(b)),
		get_var_elem(v), get_var_elem(v+1), elem_closep}, {3}};
}

/*#define from_string_lex(rel, lex, n) raw_rule({ false, { \
		elem(elem::SYM, rel), \
		elem_openp, \
		elem(elem::SYM, dict.get_lexeme(lex)), \
		elem(n), elem(n+1), \
		elem_closep},{3}})

void driver::transform_string(const wstring& s, raw_prog& r, int_t rel) {
	for (int_t n = 0; n < (int_t)s.size(); ++n) {
		r.r.push_back(raw_rule(raw_term{
			false, {
			elem(elem::SYM, dict.get_rel(rel)),
			elem_openp, elem_openp, elem_openp, elem(n),
			elem_closep, elem_closep, elem_openp, elem(s[n]),
			elem_closep, elem_openp, elem_openp, elem(n+1),
			elem_closep, elem_closep, elem_closep},{}}));
		r.r.back().h[0].calc_arity();
		if (iswspace(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"space", n));
		if (iswdigit(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"digit", n));
		if (iswalpha(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"alpha", n));
		if (iswalnum(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"alnum", n));
		if (iswprint(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"printable", n));
	}
}*/

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
		if (p.p.size() != 2 || !(p.p[1].e == L"null"))
			for (size_t n = 1; null && n != p.p.size(); ++n)
				null &= has(nullables, p.p[n]);
		if (null) nullables.insert(p.p[0]);
	}
	if (sz != nullables.size()) goto loop1;
	set<production> t;
	for (auto p : s)
		if (p.p.size() == 2 && p.p[1].e == L"null")
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

void driver::transform_grammar(raw_prog& r, lexeme rel, size_t len) {
	if (r.g.empty()) return;
	static const set<wstring> b =
		{ L"alpha", L"alnum", L"digit", L"space", L"printable"};
	for (size_t k = 0; k != r.g.size();) {
		if (r.g[k].p.size()<2)parse_error(err_empty_prod,r.g[k].p[0].e);
		size_t n = 0;
		while (n<r.g[k].p.size() && r.g[k].p[n].type != elem::ALT) ++n;
		if (n == r.g[k].p.size()) { ++k; continue; }
		r.g.push_back(
			{vector<elem>(r.g[k].p.begin(), r.g[k].p.begin() + n)});
		r.g.push_back(
			{vector<elem>(r.g[k].p.begin()+n+1, r.g[k].p.end())});
		r.g.back().p.insert(r.g.back().p.begin(), r.g[k].p[0]);
		r.g.erase(r.g.begin() + k);
	}
	for (production& p : r.g) {
		for (size_t n = 0; n < p.p.size(); ++n)
			if (p.p[n].type == elem::STR) {
				lexeme l = p.p[n].e;
				p.p.erase(p.p.begin() + n);
				bool esc = false;
				for (cws s = l[0]+1; s != l[1]-1; ++s)
					if (*s == L'\\' && !esc) esc=true;
					else p.p.insert(p.p.begin()+n++,
						elem(*s)),esc=false;
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
	m = fro_grammar_elem({elem::SYM,0,dict.get_lexeme(L"null")},1,1);
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
		if (p.p.size() == 2 && p.p[1].e == L"null") {
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
				wstring str = lexeme2str(p.p[n].e);
				if (has(b, str))
					l.b.back().push_back(from_grammar_elem_builtin(
						rel, str,n)), ++v;
				else l.b.back().push_back(
					from_grammar_elem(p.p[n],n,n+1));
			}
		}
		r.r.push_back(l);
	}
	raw_term t;
	append_sym_elem(t.e, get_lexeme(L"S")), append_openp(t.e),
	t.e.push_back(elem((int_t)0)), t.e.push_back(elem((int_t)len)),
	append_closep(t.e), t.calc_arity();
	raw_rule rr;
	rr.type = raw_rule::GOAL, rr.h = {t}, r.r.push_back(rr);
	DBG(o::out()<<"transformed grammar:"<<endl<<r;)
//#ifdef BWD_GRAMMAR
	//transform_bwd(r);
//	transform_bin(r);
//#endif
//	r.delrel = dict_get_rel(L"try");
//	return transform_string(s, r, d.rel), array<raw_prog, 2>{ r, _r };
}

/*void driver::insert_goals(raw_prog& r, const std::vector<raw_rule>& g) {
	for (const raw_rule& t : g) {
		raw_term gg;
		cat_relsym_openp(gg, L"G"), cat(gg.e, t.head(0).e),
		term_close(gg), r.r.emplace_back(gg, t.head(0));
	}
}

void driver::transform_proofs(raw_prog& r, const lexeme& rel) {
	set<raw_rule> s;
	for (auto x : r.r) {
		if (!x.nbodies()) continue;
		size_t n = 0;
nexthead:	const raw_term &head = x.head(n);
		if (head.neg) parse_error(err_proof, head.e[0].e);
		raw_rule y; // W((h)(b1)(b2)...):-h,b1,b2...
		y.add_body(head);
		for (const raw_term& t : x.bodies())
			if (t.neg) parse_error(err_proof, t.e[0].e);
			else y.add_body(t);
		y.add_head({}), cat_relsym_openp(y.head(0), rel);
		cat_in_brackets(y.head(0), head);
		for (const raw_term& t:x.bodies()) cat_in_brackets(y.head(0),t);
		term_close(y.h[0])), s.insert(y);
		if (++n < x.h.size()) goto nexthead;
	}
	for (auto x : s) r.r.push_back(x);
}*/

/*raw_term driver::get_try_pred(const raw_term& x) {
	static elem tr(elem::SYM, dict.get_lexeme(L"try"));
	raw_term t;
	return	t.e.push_back(tr), append_openp(t.e),
		t.e.insert(t.e.begin()+2, x.e.begin(), x.e.end()),
		append_closep(t.e), t.calc_arity(), t;
}

void driver::transform_bwd(const raw_term& h, const vector<raw_term>& b,
	set<raw_rule>& s) {
	raw_rule r;
	r.h = {h}, r.b = {b};
//	for (const raw_term& x : b) r.h.push_back(get_try_pred(x));
	r.b[0].insert(r.b[0].begin(), get_try_pred(h)), s.insert(move(r));
	for (const raw_term& x : b) {
		raw_rule rr;
		rr.h = {get_try_pred(x)};
		rr.b = {{get_try_pred(h)}};
		s.insert(move(rr));
	}
}

void driver::transform_bwd(raw_prog& p) {
	set<raw_rule> s;
	std::vector<raw_term> g;
	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::GOAL) {
			raw_rule x;
			x.h = {get_try_pred(r.h[0])}, s.insert(x);
		} else if (r.b.empty()) s.insert(r);
		else for (const raw_term& h : r.h)
			for (const vector<raw_term>& b : r.b)
				transform_bwd(h, b, s);
	p.r.clear();
	for (const raw_rule& r : s) p.r.push_back(r);
}*/

/*elem rep(const elem& e, map<elem, elem>& m) {
	if (e.type != elem::VAR) return e;
	auto it = m.find(e);
	return it == m.end() ? e : rep(it->second, m);
}

bool rep(const elem& x, const elem& y, map<elem, elem>& m) {
	if (x == y) return true;
	elem rx, ry;
	if (x.type != elem::VAR)
		return	y.type == elem::VAR &&
			((ry = rep(y, m)).type != elem::VAR ? x == ry :
			(m.emplace(ry, x), true));
	else if (y.type != elem::VAR)
		return	(rx = rep(x, m)).type != elem::VAR ? y == rx :
			(m.emplace(rx, y), true);
	else return	(rx = rep(x, m)) != x ? rep(rx, y, m) :
			(ry = rep(y, m)) != y ? rep(x, ry, m) : ry < rx ?
			m.emplace(ry, rx), true : (m.emplace(rx, ry), true);
}

bool unify(const raw_term& x, const raw_term& y, map<elem, elem>& m) {
	if (x.e.size() != y.e.size()) return false;
	for (size_t n = 0; n != x.e.size(); ++n)
		if (!rep(x.e[n], y.e[n], m)) return false;
	return true;
}

raw_term sub(const raw_term& x, map<elem, elem>& m) {
	raw_term r;
	for (size_t n = 0; n != x.e.size(); ++n) r.e.push_back(rep(x.e[n], m));
	return r.calc_arity(), r;
}

bool specialize(const raw_rule& r, const raw_term& t, raw_rule& res) {
	if (r.b.empty()) return res.h = r.h, true;
//	DBG(o::out() << L"specializing" << endl << r << "wrt" << endl << t <<endl;)
	for (const raw_term& h : r.h) {
		map<elem, elem> m;
		if (!unify(h, t, m)) continue;
		res.h.push_back(sub(h, m));
		for (const auto& a : r.b) {
			res.b.emplace_back();
			for (const raw_term& b : a)
				res.b.back().push_back(sub(b, m));
		}
	}
	if (res.h.size()) goto pass;
//	DBG(o::out() << L" failed " << endl;)
	return false;
pass:	//DBG(o::out() << L" returned " << res << endl;)
	return true;
}*/

#ifdef TRANSFORM_BIN_DRIVER
typedef pair<raw_term, vector<raw_term>> frule;

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

wostream& operator<<(wostream& os, const flat_rules& f) {
	for (auto x : f) os << raw_rule(x.first, x.second) << endl;
	return os;
}
#endif
/*
template<typename T> struct nullable {
	const bool null;
	const T t;
	nullable() : null(true), t(0) {}
	nullable(const T& t) : null(false), t(t) {}
//	nullable<t>& operator=(const T& x) { return null=false, t=x, *this; }
	bool operator<(const nullable<T>& x) const {
		return null ? !x.null : x.null ? false : t < x.t;
	}
};

// implementation of bottom-up subsumptive demand transform, section 4 from
// "More Efficient Datalog Queries: Subsumptive Tabling Beats Magic Sets"
// by Tekle&Liu https://www3.cs.stonybrook.edu/~tuncay/papers/TL-SIGMOD-11.pdf
// (unfinished implementation)

struct pattern {
	elem p;
	ints ar;
	nullable<size_t> n, r;
	bool g = true;
	bools s; // true for b, false for f
//	pattern() {}
	pattern(const elem& p, const ints& ar, size_t n, size_t r, bool g) :
		p(p), ar(ar), n(n), r(r), g(g) {}
	pattern(const raw_term& h, const vector<raw_term>& b, size_t n,
		size_t r, bool g) : p(h.e[0]), ar(h.arity), n(n), r(r), g(g) {
		set<elem> lvars;
		for (const elem& e : h.e)
			if (e.type == elem::VAR) lvars.insert(e);
		for (size_t i = 0; i != n; ++i)
			for (size_t j = 0; j != b[i].e.size(); ++j)
				if (b[i].e[j].type == elem::VAR)
					lvars.insert(b[i].e[j]);
		for (size_t k = 1; k != b[n].e.size(); ++k)
			if (!b[n].e[k].is_paren())
				s.push_back(b[n].e[k].type != elem::VAR ||
					!lvars.insert(b[n].e[k]).second);
	}
	pattern(const raw_term& q) : p(q.e[0]), ar(q.arity) {
		for (size_t n = 1; n != q.e.size(); ++n)
			if (!q.e[n].is_paren())
				s.push_back(q.e[n].type != elem::VAR);
	}
	static bool contains(raw_term x, vector<raw_term> y, size_t n) {
		while (n--) if (y[n] == x) return true;
		return false;
	}
	static bool subset(vector<raw_term> small, size_t ns,
		vector<raw_term> big, size_t nb) {
		if (ns > nb) return false;
		while (ns--) if (!contains(small[ns], big, nb)) return false;
		return true;
	}
	bool subsumes(const pattern& t, const flat_rules& f) const {
		// *this subsumes t
		if (!g) return false;
		bool bb = false;
		for (bool b : s) bb |= b;
		if (!bb) return true;
		for (size_t k = 0; k != s.size(); ++k)
			if (s[k]) bb &= t.s.size() > k && t.s[k];
		if (!bb || t.n < n) return false;
		return n.null||subset(f[r.t].second,n.t,f[t.r.t].second,t.n.t);
	}
};

map<pair<elem, ints>, set<bools>> get_patterns(const flat_rules& f) {
	vector<pattern> v;
	function<void(const pattern&)> on_new_pat;
	on_new_pat = [&f, &v, &on_new_pat](const pattern& p) {
		v.push_back(p);
		for (size_t r2 : f.m.at({p.p, p.ar})) {
			const vector<raw_term>& a = f[r2].second;
			for (size_t j = 0; j != a.size(); ++j) {
				const raw_term& b = a[j];
				if (f.m.find({b.e[0],b.arity}) == f.m.end())
					continue;
				pattern pat(f[r2].first, a, j, r2, p.g && !j);
				for (const pattern& q : v)
					if (q.subsumes(pat, f)) return;
				on_new_pat(pat);
			}
		}
	};
	on_new_pat(pattern(f.q));
	map<pair<elem, ints>, set<bools>> r;
	for (const pattern& p : v) r[{p.p, p.ar}].insert(p.s);
	return r;
}*/

/*void driver::refresh_vars(raw_prog& p) {
	set<raw_rule> rs;
	for (raw_rule r : p.r) {
		auto s1 = refresh_vars(r);
		rs.insert(s1.begin(), s1.end());
	}
	p.r.clear();
	for (auto x : rs) p.r.push_back(x);
}

set<raw_term> driver::get_queries(const raw_prog& p) {
	set<raw_term> qs;
	map<elem, elem> m;
	size_t v = 1;
	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::GOAL) {
			assert(r.h.size() == 1);
			raw_term t = r.h[0];
			m.clear(), v = 1, refresh_vars(t, v, m), qs.insert(t);
		}
	return qs;
}*/

/*lexeme driver::get_demand_lexeme(elem e, const ints& i, const bools& b) {
	wstring s;
	for (int_t j : i) s += to_wstring(j);
	s += L'_';
	for (bool x : b) s += x ? L'b' : L'f';
	return dict.get_lexeme(wstring(L"d_") + lexeme2str(e.e) + s);
}

#define get_demand_elem(t, b)\
	elem(elem::SYM, get_demand_lexeme(t.e[0], t.arity, b))

raw_prog driver::transform_sdt(const raw_prog& p) {
	const flat_rules f(p, *this);
	const map<pair<elem, ints>, set<bools>> pats = get_patterns(f);
	raw_prog r;
	for (const auto& x : f) {
		if (x.second.empty()) { r.r.push_back(x.first); continue; }
		for (const bools& b : pats.at({x.first.e[0], x.first.arity})) {
			r.r.emplace_back(), r.r.back().h = {x.first},
			r.r.back().b = {x.second};
			raw_term d;
			d.e.push_back(get_demand_elem(x.first, b)),
			append_openp(d.e);
			for (size_t n = 1, k = 0; n != x.first.e.size(); ++n)
				if (x.first.e[n].type == elem::VAR && b[k++])
					d.e.push_back(x.first.e[n]);
			append_closep(d.e), d.calc_arity();
			vector<raw_term> &t = r.r.back().b.back();
			t.insert(t.begin(), move(d));
		}
	}
	DBG(o::out()<<"sdt transform, input:"<<endl<<p<<endl;)
	DBG(o::out()<<"sdt transform, output:"<<endl<<r<<endl;)
	return r;
}*/
#ifdef TRANSFORM_BIN_DRIVER
lexeme driver::get_new_rel() {
	static size_t last = 1;
	wstring s = L"r";
	size_t sz;
	lexeme l;
retry:	sz = rels.size(), l = get_lexeme(s + to_wstring(last));
	rels.insert(l);
	if (rels.size() == sz) { ++last; goto retry; }
	return l;
}

void driver::transform_bin(raw_prog& p) {
	flat_rules f(p, *this);
	for (const frule& r : f) {
		rels.insert(r.first.e[0].e);
		for (const raw_term& t : r.second) rels.insert(t.e[0].e);
	}
//	DBG(o::out()<<"bin before:"<<endl<<f<<endl;)
	for (const raw_rule& r : p.r)
		if (r.b.empty() && r.type == raw_rule::NONE)
			f.push_back({r.h[0], {}}),
			assert(r.h[0].e.size()),
			assert(f.back().first.e.size());
	p.r.clear();
	auto interpolate = [this](
		const vector<raw_term>& x, set<elem> v) {
		raw_rule r;
		r.b = {x}, r.h.emplace_back();
		r.h[0].e.emplace_back(elem::SYM, get_new_rel());
		append_openp(r.h[0].e);
		for (size_t k = 0; k != x.size(); ++k)
			for (size_t n = 0; n != x[k].e.size(); ++n)
				if (has(v, x[k].e[n]))
					r.h[0].e.push_back(x[k].e[n]),
					v.erase(x[k].e[n]);
		return append_closep(r.h[0].e), r.h[0].calc_arity(), r;
	};
	for (auto x : f) {
		while (x.second.size() > 2) {
			set<elem> v;
			for (size_t n = 2, k; n != x.second.size(); ++n)
				for (k = 0; k != x.second[n].e.size(); ++k)
					if (x.second[n].e[k].type == elem::VAR)
						v.insert(x.second[n].e[k]);
			for (size_t k = 0; k != x.first.e.size(); ++k)
				if (x.first.e[k].type == elem::VAR)
					v.insert(x.first.e[k]);
			raw_rule r = interpolate(
				{ x.second[0], x.second[1] }, move(v));
			x.second.erase(x.second.begin(), x.second.begin() + 2);
			x.second.insert(x.second.begin(), r.h[0]);
			p.r.push_back(move(r));
		}
		p.r.emplace_back(x.first, x.second);
//		for (auto x : p.r.back().b) assert(!x.empty());
	}
	if (f.q.e.size()) p.r.emplace_back(raw_rule::GOAL, f.q);
}
#endif

/*raw_prog driver::reify(const raw_prog& p) {
	set<raw_rule> s;
	set<lexeme> rels;
	for (const raw_rule& r : p.r) {
		for (const raw_term& t : r.h) rels.emplace(t.e[0]);
		for (const auto& x : r.b)
			for (const raw_term& y : x)
				rels.emplace(x.e[0]);
	}
	elem relname = elem(elem::SYM, dict.get_lexeme(L"relname"));
	elem fact = elem(elem::SYM, dict.get_lexeme(L"fact"));
	elem rule = elem(elem::SYM, dict.get_lexeme(L"rule"));
	lexeme op = dict.get_lexeme(L"("), cp = dict.get_lexeme(L")");
	raw_term t;
	for (const lexeme& l : rels)
		t.e = { r, elem_openp, l, elem_closep },
		t.calc_arity(), s.emplace(t), t.clear();
	set<sizes> lens;
	set<frule> rls;
	const elem op = elem_openp, cp = elem_closep;
	auto reify_fact = [&relname, &fact, this](const raw_term& t) {
		vector<raw_term> v;
		v.push_back({ relname, op, t.e[0], cp });
		for (size_t n = 1; n != t.e.size(); ++n)
			if (t.e[n].type == VAR)
				v.push_back({ relname, op, t.e[n], cp }),
				v.back().neg = true;
		raw_term r;
		r.e = { fact, op };
		for (size_t n = 0; n != t.e.size(); ++n)

		return r.e.push_back(cp), v.push_back(r), v;
	};
	for (const raw_rule& r : p.r)
		for (const raw_term& t : r.h)
			for (const auto& x : r.b) {
				rls.emplace(t, x);
				raw_term th;
				th.e = { fact, elem_openp,
			}

}*/

/*set<raw_rule> driver::transform_ms(const set<raw_rule>& p,
	const set<raw_term>& qs) {
	set<raw_rule> s;
	raw_rule rr;
	for (const raw_term& q : qs)
		for (const raw_rule& t : p) {
			rr.clear();
			if (t.type == raw_rule::NONE && specialize(t, q, rr))
				s.insert(move(rr));
		}
	return s;
}

raw_prog driver::transform_ms(raw_prog p) {
	refresh_vars(p);
	set<raw_term> qs = get_queries(p);
	set<raw_rule> rs, pr;
	for (const raw_rule& r : p.r) pr.insert(r);
	map<elem, elem> m;
	size_t v = 1;
	while (!qs.empty()) {
		set<raw_rule> r = transform_ms(pr, qs);
		size_t sz = qs.size();
		qs.clear();
		for (raw_rule t : r)
			for (auto x : t.b)
				for (auto y : x)
					m.clear(), v = 1, refresh_vars(y, v, m),
					qs.insert(y);
		rs.insert(r.begin(), r.end());
		if (sz == qs.size()) break;
	}
	raw_prog res;
	for (const raw_rule& t : rs) res.r.push_back(t);
	DBG(o::out()<<"orig:"<<endl<<p;)
	DBG(o::out()<<"spec:"<<endl<<res;)
	return res;
}
*/
/*raw_prog driver::transform_ms(raw_prog p) { // magic sets transform
	set<raw_rule> s, ss;
	refresh_vars(p);
	set<raw_term> qs = get_queries(p);
	size_t sz, v;
	map<elem, elem> m;
loop:	sz = qs.size();
#ifdef DEBUG
	o::out()<<"qs:"<<endl;
	for (auto x : qs) o::out() << x << endl;
#endif
	for (raw_term q : qs) {
		m.clear(), v = 1, refresh_vars(q, v, m);
		for (const raw_rule& t : p.r) {
			if (t.type == raw_rule::GOAL) continue;
			raw_rule rr;
			if (specialize(t, q, rr)) {
				s.emplace(rr);
				for (auto x : rr.b) for (auto y : x) qs.insert(y);
			}
		}
	}
	if (sz != qs.size()) goto loop;
	raw_prog r;
	for (const raw_rule& t : s) r.r.push_back(t);
	DBG(o::out()<<"orig:"<<endl<<p;)
	DBG(o::out()<<"spec:"<<endl<<r;)
	return r;
}*/
