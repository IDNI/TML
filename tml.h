#include <vector>
#include <map>
#include <set>
#include <cstring>
#include <cstdint>
#include <iostream>
using namespace std;

#ifdef _DEBUG
#define DEBUG(x) (wcout<<x).flush()
#else
#define DEBUG(x)
#endif

typedef map<int32_t, int32_t> env;

struct literal : public vector<int32_t> {
	typedef vector<int32_t> base;
	using base::base;
	set<int> vars;
	literal() {}
	literal(const literal &, env& e);

	friend wostream& operator<<(wostream &os, const literal&);
	int operator<(const literal &l) const;
	bool unify(const literal &g, env &e) const;
	bool operator==(const literal&) const;
};

struct clause : public vector<literal*> {
	typedef vector<literal*> base;
	using base::base;
	set<int> vars, rels;
	clause() {}
	clause(const clause&, env&);

	clause& operator+=(const literal &t);
	friend wostream& operator<<(wostream &os, const clause&);
	bool operator==(const clause&) const;
	virtual ~clause();
};

class dict_t {
	vector<wstring> strings;
	map<wstring, size_t> m;
public:
	int32_t operator[](const wstring&);
	wstring operator[](int32_t) const;
	friend wostream& operator<<(wostream &os, const dict_t&);
};

extern dict_t dict;

class dlp : public vector<const clause*> { // disjunctive logic program
	const wchar_t *in;
	typedef map<int32_t, map<size_t, size_t>> index_t;
	index_t index;

	bool word_read(int32_t&);
	bool literal_read(clause&, bool negate);
	bool clause_read();
	void program_read();

	void pe(const clause*, const literal*, const literal*, dlp&);
public:
	void program_read(wistream&);
	void pe(dlp&);
	void index_write(wostream&) const;
	friend wostream& operator<<(wostream&, const dlp&);
	dlp& operator+=(clause*);
	virtual ~dlp();
};

wostream& operator<<(wostream &os, const env &e);
