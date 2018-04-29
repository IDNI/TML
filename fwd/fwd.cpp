#include "fwd.h"
#include <cstdlib>

#define envclear(e, sz) ((tmpenv)memset((e),0,sz*sizeof(int_t)))
#define mkenv(sz) envclear(alloca(sz*sizeof(int_t)), sz)
#define dup(e, sz) env(e, &e[sz])

int_t rep(const tmpenv& e, int_t x) {
	return x>0||!e[-x-1]||e[-x-1]==x?x: rep(e,e[-x-1]);
} 

int_t rep(tmpenv& e, int_t x){
	return x>0||!e[-x-1]||e[-x-1]==x?x:e[-x-1]= rep(e,e[-x-1]);
}

bool rep(tmpenv& e, int_t x, int_t y) {
	if ((x = rep(e, x)) > (y = rep(e, y))) ::swap(x, y);
	return x == y || (x < 0 && (e[-x - 1] = y, true));
} 

size_t unifications = 0;
clause& operator+=(clause& c, const term& t) { return c.emplace(t), c; }
clause& operator+=(clause& x, const clause& y) { return x.insert(y.begin(), y.end()), x; }

bool unify(const term& x, const term& g, tmpenv e) {
	++unifications;
	if (x.size() != g.size()) return false;
	for (size_t n=0; n<x.size(); ++n) if (!rep(e, x[n], g[n]))
		return false;
	return true;
} 

term sub(const term& t, const tmpenv& e) {
	term r(t.size());
	for (size_t n = 0; n < t.size(); ++n)
		r[n] = (t[n] ? rep(e, t[n]) : 0);
	return r;
}

clause sub(const clause& t, const tmpenv e) {
	clause r;
	for (const term& x : t) r += sub(x, e);
	return r;
}

set<int_t> vars(const term& x) {
	set<int_t> r;
	for (int_t t : x) if (t < 0) r.emplace(t);
	return r;
}

term interpolate(const term& x, const term& y) {
	term r;
	set<int_t> vx = vars(x), vy = vars(y);
	for (	auto ix = vx.begin(), iy = vy.begin();
		ix != vx.end() && iy != vy.end();)
		if (*ix == *iy) r.push_back(*ix++), ++iy;
		else if (*ix < *iy) ++ix;
		else ++iy;
	return r;
}

void pfp::add(const term& x, const clause& h) {
	size_t nv = vars(x).size();
	for (auto r : kb)
		for (auto t : h)
			if (	tmpenv e = mkenv(nv);
				unify(t, r.first.first, e) ||
				unify(t, r.first.second, envclear(e, nv)))
				add(	sub(r.first.first, e),
					sub(r.first.second, e),
					sub(r.second, e));
}

bool pfp::add(term x, term y, clause h) {
	map<int_t, int_t> v;
	clause hh;
	size_t k = 0;
	for (size_t n = 0; n < x.size(); ++n)
		if (x[n] >= 0) continue;
		else if (auto it = v.find(x[n]); it == v.end())
			v.emplace(x[n], -++k);
		else x[n] = it->second;
	for (const term& t : h) {
		term tt = t;
		for (int_t& i : tt)
			if (i >= 0) continue;
			else if (auto it = v.find(i); it == v.end()) {
				err_head_var_not_in_body;
				return false;
			}
			else i = it->second;
		hh.emplace(tt);
	}
	kb[two<term>(x, y)] += hh; // todo: extract
	return true;
}

void test_interpolate() {
	assert(interpolate({1,-1,2,-2},{2,-3,3,-4,-2})==term{-2});
}

void pfp::add(clause x, const clause& y) {
	if (x.size() == 1) add(*x.begin(), y);
	else if (x.size() == 2) add(*x.begin(), *x.rbegin(), y);
	else {
		term i = interpolate(*x.begin(), *x.rbegin());
		kb[two<term>(*x.begin(), *x.rbegin())] += i;
		x.erase(x.begin()), x.emplace(i), add(x, y);
	}
}

void pfp::Tp(terms& add, terms& del) {/*
	for (size_t n = 0; n < b.size(); ++n) {
		set<frame> q;
		term x;
		tmpenv s = mkenv(nvars[n]);
		for (const term& t : f)
			if (	tmpenv e = mkenv(nvars[n]);
				unify(b[n][0], t, e))
				q.emplace(0, dup(e, nvars[n]));
		while (!q.empty()) {
			auto [k, e] = *q.begin();
			q.erase(q.begin());
			if (k == b[n].size()) {
				for (const term& t : h[n])
					(t[0]?add:del).emplace(
						sub(t, &e[0]));
				continue;
			}
			x = sub(b[n][k], &e[0]);
			bool g = true;
			for (auto y : x) g &= y > 0;
			if (g) {
				if (	add.find(x) != add.end() ||
					(f.find(x) != f.end() &&
					del.find(x) == del.end()))
					q.emplace(k+1, e);
			} else for (const term& t : f)
				if (s=(tmpenv)memcpy(s,&e[0],
					sizeof(int_t)*nvars[n]),
					!unify(x, t, s)) continue;
				else q.emplace(k+1, dup(s,nvars[n]));
		}
	}
	f.insert(add.begin(), add.end());
	for (auto it = del.begin(); it != del.end(); ++it)
		f.erase(term(&(*it)[1],&(*it)[it->size()]));*/
}

pfp::pfp() : nvars(0), stage(0) {}
pfp::~pfp() { if (nvars) delete[] nvars; }

size_t pfp::operator()(terms& r, size_t &steps) {
/*	if (nvars) delete[] nvars;
	nvars = new size_t[b.size()];
	for (size_t n = 0; n < b.size(); ++n) normrule(n);
	for (; stage < steps; ++stage) step(r, steps);*/
	return steps;
}

void pfp::normrule(size_t n) {
/*	map<int_t, int_t> v;
	size_t nv = 1;
	for (size_t k = 0; k < b[n].size(); ++k)
		for (size_t j = 0; j < b[n][k].size(); ++j)
			if (b[n][k][j] > 0) continue;
			else if (auto it=v.find(b[n][k][j]);it==v.end())
				v.emplace(b[n][k][j], -nv),
				b[n][k][j] = -nv++;
//				dict.oldvars[n][-nv] = b[n][k][j],
			else b[n][k][j] = it->second;
	for (term& i : h[n]) for (int_t& j : i) if (j < 0) j = v[j];
	nvars[n] = nv - 1;*/
}

void pfp::step(terms& r, size_t& l) {
	terms add, del, lf = f;
	Tp(add, del);
	if (f == lf) l = stage;
	else if (auto it = stages.emplace(f, stages.size()); !it.second)
		l = it.first->second;
	r = f;
}

wostream& operator<<(wostream& os, const term& t) {
	for (auto x : t) os << dict(x) << L' ';
	return os;
}

wostream& operator<<(wostream& os, const set<term>& s) {
	size_t sz = s.size();
	for (auto t : s) os << t << (--sz ? ", " : "");
	return os;
}

wstring repl::get_line() const {
	wstring r;
	if (!getline(wcin, r)) {
		cout << "end of input, exiting" << endl; exit(0); }
	while (iswspace(r[0])) r.erase(0);
	while (iswspace(r[r.size() - 1])) r.erase(r.size() - 1);
	return r;
}

bool repl::walnum(wchar_t ch) const { return ch == L'?' || iswalnum(ch); }

int_t repl::peek_word(const wchar_t* s) const {
	while (iswspace(*s)) ++s;
	size_t n;
	for (n = 0; walnum(s[n]); ++n);
	return dict(wstring(s, n));
}

int_t repl::get_word(const wchar_t** s) const {
	while (iswspace(**s)) ++*s;
	size_t n;
	for (n = 0; walnum((*s)[n]); ++n);
	size_t r = dict(wstring(*s, n));
	*s += n;
	return r;
}

term repl::get_term(const wchar_t** line) const {
	term r;
	for (; **line && **line != L'.';)
		if (**line == L',') return ++*line, r;
		else if (peek_word(*line) == thenword) return r;
		else r.push_back(get_word(line));
	return r;
}

clause repl::get_clause(const wchar_t** line) {
	clause r;
	for (; **line && **line != L'.';) {
		while (iswspace(**line)) ++*line;
		if (!**line || peek_word(*line) == thenword) return r;
		if (term t = get_term(line); !t.size()) return r;
		else r += t;
	}
	if (**line == L'.') ++*line;
	return r;
}

void repl::run(const wchar_t* line) {
	wstring w;
	while (iswspace(*line)) ++line;
	if (!*line) return;
	if (peek_word(line) == ifword) {
		get_word(&line);
		clause b = get_clause(&line);
		if (get_word(&line) != thenword)
			throw runtime_error("'then' expected");
		clause h = get_clause(&line);
		p.add(b, h);
	} else for (const term& t : get_clause(&line)) p.add(t);
}

repl::repl() : ifword(dict(L"if")), thenword(dict(L"then")) {}

void repl::run() {
	for (wstring line;;)
		if ((line = get_line()) == L"run") {
			terms t;
			size_t steps = WINT_MAX, n;
			n = p(t, steps);
			if (n == steps) wcout << "pass after " <<
					steps << " steps" << endl;
			else 	wcout << "fail, step " << n <<
				" same as step " << steps << endl;
			wcout << t.size() << ' ' << unifications << endl;
//			for (auto x : t) wcout << x << endl;
		} else if (line.substr(0, 4) == L"step") {
			const wchar_t *s = line.c_str() + 4;
			wchar_t *e;
			while (iswspace(*s)) ++s;
			size_t steps = wcstoul(s, &e, 10);
			if (!e) {
				wcout << "usage: step <# of steps>";
				continue; }
			terms t;
			size_t n = p(t, steps);
			if (n == steps) wcout << "pass after " <<
					steps << " steps" << endl;
			else 	wcout << "fail, step " << n <<
				" same as step " << steps << endl;
			for (auto x : t) wcout << x << endl;
		} else run(line.c_str());
}

int main(int, char**) {
	setlocale(LC_ALL, "");
	test_interpolate();
	repl r;
	r.run();
}
