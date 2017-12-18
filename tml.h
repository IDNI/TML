#include <vector>
#include <map>
#include <set>
#include <cstring>
#include <cstdint>
#include <iostream>
#include <algorithm>
using std::vector;
using std::map;
using std::set;
using std::wstring;
using std::wstringstream;
using std::wcout;
using std::wcin;
using std::wcerr;
using std::wistream;
using std::wostream;
using std::pair;
using std::endl;
using std::runtime_error;

#ifdef _DEBUG
#define DEBUG(x) (wcout<<x).flush()
#else
#define DEBUG(x)
#endif

class dict_t {
	vector<wstring> strings;
	map<wstring, size_t> m;
public:
	int32_t operator[](const wstring&);
	wstring operator[](int32_t) const;
	friend wostream& operator<<(wostream &os, const dict_t&);
};
extern dict_t dict;

struct strbuf {
	const wchar_t *s;
	strbuf(const wchar_t *s) : s(s) {}
	strbuf& operator++() { ++s; return *this; }
	wchar_t operator*() const { return *s; }
	intptr_t operator-(const strbuf& t) const { return s - t.s; }
	wchar_t adv() { return *s++; }
};

template<typename T = uint64_t>
struct hash {
	typedef const unsigned char* buf;
	struct hashcmp {
		bool operator()(const hash<T> &x, const hash<T> &y) const {
			return x.h < y.h;
		}
	};
	T h = 0;
	void operator()(buf s, size_t sz) {
		while (sz--) h = *s+++((h<<6)+(h<<16));
	}
	void operator()(const hash<T> &h) { (*this)((buf)&h, sizeof(hash<T>)); }
	void clear() { h = 0; }
};

typedef map<int32_t, int32_t> env;
class literal : protected vector<int32_t> {
	const int32_t* prel() const { return &((*((base*)this))[0]); }
	const int32_t* parg() const { return &((*((base*)this))[1]); }
	int32_t* prel() { return &((*((base*)this))[0]); }
	int32_t* parg() { return &((*((base*)this))[1]); }
	typedef vector<int32_t> base;
public:
	hash<> h;
	literal() : base() {}
	literal(size_t sz) : base(sz) {}
	literal(const literal &, env& e);

	void push_back(int32_t i);
	void clear() { base::clear(); }
	void flip();

	bool same_atom(const literal &l) const;
	int32_t rel() const { return at(0); }
	friend wostream& operator<<(wostream &os, const literal&);
	int operator<(const literal &l) const;
	size_t size() const { return base::size(); }
	bool unify(const literal &g, env &e) const;
	bool operator==(const literal&) const;
	bool operator!=(const literal& l) const { return !(l==*(this)); }
};

class clause : protected vector<literal*> {
	typedef vector<literal*> base;
	void rehash() { h.clear(); for (literal *l : *this) h(l->h); }
public:
	clause() {}
	clause(const clause&, env&);
	hash<> h;

	void sort() { std::sort(begin(), end()); rehash(); }
	clause& operator+=(const literal &t);
	void flip() { for (literal *l : *this) l->flip(); rehash(); }
	void clear() { base::clear(), h.h = 0; }

	size_t size() const { return base::size(); }
	int32_t lastrel() const { return back()->rel(); }
	const literal* at(size_t k) const { return base::at(k); }
	friend wostream& operator<<(wostream &os, const clause&);
	bool operator==(const clause&) const;
	virtual ~clause();
};

class dlp : protected vector<const clause*> { // disjunctive logic program
	typedef map<int32_t, map<size_t, size_t>> index_t;
	index_t index;

	bool word_read(strbuf&, int32_t&);
	bool literal_read(strbuf&, clause&, bool negate);
	bool clause_read(strbuf&);
	void program_read(strbuf&);

	void pe(const clause*, const literal*, const literal*, dlp&);

	hash<> rehash() {
		hash<> h;
		sort(begin(), end());
		for (const clause *c : *this) h(c->h);
		return h;
	}
public:
	void program_read(wistream&);
	void pe(dlp&);
	void index_write(wostream&) const;
	friend wostream& operator<<(wostream&, const dlp&);
	dlp& operator+=(clause*);
	virtual ~dlp();
};

wostream& operator<<(wostream &os, const env &e);
