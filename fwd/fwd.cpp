#include "fwd.h"
#include <cstdlib>
#define mkenv(sz) ((tmpenv)memset(alloca(sz*sizeof(int_t)),0,sz*sizeof(int_t)))
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

bool unify(const term& x, const term& g, tmpenv& e) {
	if (x.size() != g.size()) return false;
	for (size_t n=0; n<x.size(); ++n) if (!rep(e, x[n], g[n])) return false;
	return true;
} 

term sub(const term& t, const tmpenv& e) {
	term r(t.size());
	for (size_t n = 0; n < t.size(); ++n) r[n] = (t[n] ? rep(e, t[n]) : 0);
	return r;
}

void pfp::Tp(terms& add, terms& del) {
	for (size_t n = 0; n < b.size(); ++n) {
		set<frame> q;
		term x;
		tmpenv s = mkenv(nvars[n]);
		for (const term& t : f)
			if (tmpenv e = mkenv(nvars[n]); unify(b[n][0], t, e))
				q.emplace(0, dup(e, nvars[n]));
		while (!q.empty()) {
			auto [k, e] = *q.begin();
			q.erase(q.begin());
			x = sub(b[n][k], &e[0]);
			for (const term& t : f)
				if (s=(tmpenv)memcpy(s,&e[0],sizeof(int_t)*nvars[n]),
					!unify(x, t, s)) continue;
				else if (k+1 < b[n].size())
					q.emplace(k+1, dup(s,nvars[n]));
				else for (const term& t : h[n])
					(t[0]?add:del).emplace(sub(t, &e[0]));
		}
	}
	f.insert(add.begin(), add.end());
	for (auto it = del.begin(); it != del.end(); ++it)
		f.erase(term(&(*it)[1],&(*it)[it->size()]));
}

pfp::pfp() : nvars(0), stage(0) {}
pfp::~pfp() { if (nvars) delete[] nvars; }

size_t pfp::operator()(terms& r, size_t &steps) {
	if (nvars) delete[] nvars;
	nvars = new size_t[b.size()];
	for (size_t n=0; n<b.size(); ++n) normrule(n);
	for (; stage < steps; ++stage) step(r, steps);
	return steps;
}

void pfp::normrule(size_t n) {
	map<int_t, size_t> v;
	size_t nv = 1;
	for (size_t k = 0; k < b[n].size(); ++k)
		for (size_t j = 0; j < b[n][k].size(); ++j)
			if (b[n][k][j] > 0) continue;
			else if (auto it = v.find(b[n][k][j]); it == v.end())
				v.emplace(b[n][k][j], nv),
				dict.oldvars[-nv] = b[n][k][j],
				b[n][k][j] = -nv++;
			else
				b[n][k][j] = -b[n][k][it->second - 1];
	for (term& i : h[n]) for (int_t& j : i) if (j < 0) j = -v[j];
	nvars[n] = nv - 1;
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
	if (!getline(wcin, r)) { cout << "end of input, exiting" << endl; exit(0); }
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

vector<term> repl::get_clause(const wchar_t** line) {
	vector<term> r;
	for (; **line && **line != L'.';) {
		while (iswspace(**line)) ++*line;
		if (!**line || peek_word(*line) == thenword) return r;
		if (term t = get_term(line); !t.size()) return r;
		else r.push_back(t);
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
		p.b.push_back(b), p.h.push_back(h);
	} else for (const term& t : get_clause(&line))
		p.f.emplace(t);
}

repl::repl() : ifword(dict(L"if")), thenword(dict(L"then")) {}

void repl::run() {
	for (wstring line;;)
		if ((line = get_line()) == L"run") {
			terms t;
			size_t steps = WINT_MAX, n;
			n = p(t, steps);
			if (n == steps) wcout << "pass after " << steps << " steps" << endl;
			else wcout << "fail, step " << n << " same as step " << steps << endl;
			for (auto x : t) wcout << x << endl;
		} else if (line.substr(0, 4) == L"step") {
			const wchar_t *s = line.c_str() + 4;
			wchar_t *e;
			while (iswspace(*s)) ++s;
			size_t steps = wcstoul(s, &e, 10);
			if (!e) { wcout << "usage: step <# of steps>"; continue; }
			terms t;
			size_t n = p(t, steps);
			if (n == steps) wcout << "pass after " << steps << " steps" << endl;
			else wcout << "fail, step " << n << " same as step " << steps << endl;
			for (auto x : t) wcout << x << endl;
		} else run(line.c_str());
}

void add_rule(set<term> b, set<term> h) { wcout << b << L" => " << h << endl; }
void add_fact(term t) { wcout << t << endl; }

int main(int, char**) {
	setlocale(LC_ALL, "");
	repl r;
	r.run();
}
