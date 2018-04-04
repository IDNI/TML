#include <array>
#include <vector>
#include <set>
#include <map>
#include <alloca.h>
#include <cstring>
#include <cassert>
#include <stdexcept>
#include <iostream>
using namespace std;
template<typename T> using two = array<T, 2>;
typedef int32_t int_t;
typedef vector<int_t> term;
typedef vector<term> clause;
typedef vector<clause> clauses;
typedef two<size_t> loc;
typedef set<loc> locs;
typedef set<term> terms;
typedef int_t* tmpenv;
typedef vector<int_t> env;
typedef pair<size_t, env> frame;
wostream& operator<<(wostream& os, const term& t);
wostream& operator<<(wostream& os, const set<term>& s);

class pfp {
	size_t* nvars;
	void Tp(terms& add, terms& del);
public:
	size_t operator()(terms&, size_t&);
	terms f;
	clauses b, h;
	pfp();
	~pfp();
};

class dict_t {
	map<wstring, int_t> m;
	vector<wstring> v;
public:
	map<int_t, int_t> oldvars;
	dict_t() { m.emplace(L"not", 0); }
	int_t operator()(const wstring& s) {
		assert(s.size());
		if (auto it = m.find(s); it != m.end()) return it->second;
		v.push_back(s);
		return m.emplace(s,s[0]==L'?'?-v.size():v.size()).first->second;
	}
	wstring operator()(int_t x) const {
		if (x < 0)
			if (auto it = oldvars.find(x); it != oldvars.end())
				x = it->second;
		return x ? v[abs(x) - 1] : L"not";
	}
} dict;

class repl {
	pfp p;
	const int_t ifword, thenword;
	wstring get_line() const;
	bool walnum(wchar_t ch) const;
	int_t peek_word(const wchar_t* s) const;
	int_t get_word(const wchar_t** s) const;
	term get_term(const wchar_t** line) const;
	void add_rule(set<term> b, set<term> h);
	void add_fact(term t);
	vector<term> get_clause(const wchar_t** line);
	void run(const wchar_t* line);
public:
	repl();
	void run();
};
