#include <map>
#include <vector>
#include <cstdint>
#include "hash.h"

using std::map;
using std::vector;
using std::wostream;

typedef map<int32_t, int32_t> env;

class literal : protected vector<int32_t> {
	const int32_t* prel() const;
	const int32_t* parg() const;
	int32_t* prel();
	int32_t* parg();
	typedef vector<int32_t> base;
public:
	uint64_t hash;
	literal();
	literal(size_t sz);
	literal(const literal&);
	literal(const literal&, env&);

	void push_back(int32_t i);
	void clear();
	void flip();
	uint64_t rehash();

	int32_t at(size_t k) const;
	bool same_atom(const literal &l) const;
	int32_t rel() const;
	friend wostream& operator<<(wostream &os, const literal&);
	int operator<(const literal &l) const;
	size_t size() const;
	bool unify(const literal &g, env &e) const;
	bool operator==(const literal&) const;
	bool operator!=(const literal& l) const;
};

