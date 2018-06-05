#include "repl.h"
#include <cstdlib>

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
		else r.insert(t);
	}
	if (**line == L'.') ++*line;
	return r;
}

void repl::parse(const wchar_t* line) {
	while (iswspace(*line)) ++line;
	if (!*line) return;
	if (peek_word(line) == ifword) {
		get_word(&line);
		clause b = get_clause(&line);
		if (get_word(&line) != thenword) throw runtime_error("'then' expected");
		p.add(b, get_clause(&line));
	} else for (const term& t : get_clause(&line)) p.add(t);
}

repl::repl() : ifword(dict(L"if")), thenword(dict(L"then")) {}

void repl::run() {
	for (wstring line;;)
/*		if ((line = get_line()) == L"run") {
			clause t;
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
			clause t;
			size_t n = p(t, steps);
			if (n == steps) wcout << "pass after " <<
					steps << " steps" << endl;
			else 	wcout << "fail, step " << n <<
				" same as step " << steps << endl;
			for (auto x : t) wcout << x << endl;
		} else*/
			parse(get_line().c_str());
}

int main(int, char**) {
	setlocale(LC_ALL, "");
//	test_interpolate();
	repl r;
	r.run();
}
