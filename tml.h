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

class dict_t {
	vector<wstring> strings;
	map<wstring, size_t> m;
public:
	int32_t operator[](const wstring&);
	wstring operator[](int32_t) const;
	friend wostream& operator<<(wostream &os, const dict_t&);
};
extern dict_t dict;

template<typename T = uint64_t>
struct hash {
	T h = 0;
	void operator()(const unsigned char *s, size_t sz) {
		while (sz--) h = *s+++((h<<6)+(h<<16));
	}
};

typedef map<int32_t, int32_t> env;
class literal : protected vector<int32_t> {
	const int32_t* prel() const { return &((*((base*)this))[0]); }
	const int32_t* parg() const { return &((*((base*)this))[1]); }
	int32_t* prel() { return &((*((base*)this))[0]); }
	int32_t* parg() { return &((*((base*)this))[1]); }
public:
	typedef vector<int32_t> base;
	literal() {}
	literal(size_t sz) : vector<int32_t>(sz) {}
	literal(const literal &, env& e);

	bool same_atom(const literal &l) const;
	void push_back(int32_t i) { base::push_back(i); }
	void clear() { base::clear(); }
	int32_t rel() const { return at(0); }
	void flip() { *prel() = -*prel(); }
	friend wostream& operator<<(wostream &os, const literal&);
	int operator<(const literal &l) const;
	size_t size() const { return base::size(); }
	bool unify(const literal &g, env &e) const;
	bool operator==(const literal&) const;
	bool operator!=(const literal& l) const { return !(l==*(this)); }

//	hash h;
};

struct clause : public vector<literal*> {
	clause() {}
	clause(const clause&, env&);

	clause& operator+=(const literal &t);
	friend wostream& operator<<(wostream &os, const clause&);
	bool operator==(const clause&) const;
	virtual ~clause();
};

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
