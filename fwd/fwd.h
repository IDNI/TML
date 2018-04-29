#include <array>
#include <vector>
#include <set>
#include <map>
#include <variant>
#include <alloca.h>
#include <cstring>
#include <cassert>
#include <stdexcept>
#include <iostream>
using namespace std;

typedef int32_t int_t;
typedef vector<int_t> term;
typedef set<term> clause;
typedef set<clause> clauses;
typedef set<term> terms;
typedef int_t* tmpenv;
typedef vector<int_t> env;
typedef pair<size_t, env> frame;
template<typename T> using two = pair<T, T>;
wostream& operator<<(wostream& os, const term& t);
wostream& operator<<(wostream& os, const set<term>& s);

class pfp {
	size_t *nvars, stage;
	map<terms, size_t> stages;
	void normrule(size_t);
	void step(terms&, size_t&);
	void Tp(terms& add, terms& del);
	terms f;
	map<two<term>, clause> kb;
	void add(const term& x, const clause& h);
	bool add(term x, term y, clause h);
public:
	size_t operator()(terms&, size_t&);
	void add(clause x, const clause& y);
	void add(const term& t) { f.emplace(t); }
	pfp();
	~pfp();
};

class dict_t {
	map<wstring, int_t> m;
	vector<wstring> v;
public:
//	map<size_t, map<int_t, int_t>> oldvars;
	dict_t() { m.emplace(L"not", 0); }
	int_t operator()(const wstring& s) {
		assert(s.size());
		if (auto it = m.find(s); it != m.end()) return it->second;
		v.push_back(s);
		return m.emplace(s,s[0]==L'?'?-v.size():v.size()).first->second;
	}
	wstring operator()(int_t x) const {
//		if (x < 0)
//			if (oldvars.find(n) != oldvars.end())
//				if (	auto it = oldvars.at(n).find(x);
//					it != oldvars.at(n).end())
//						x = it->second;
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
	clause get_clause(const wchar_t** line);
	void run(const wchar_t* line);
public:
	repl();
	void run();
};

#define error(x) (cerr<<(x)<<endl)
#define err_head_var_not_in_body error("Variables that appear on consequences must also appear in the premises")
