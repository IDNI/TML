#include "dnf.h"

#define setbit(x, n) ((x) |= 1 << (n))
#define getbit(x, n) ((x) & (1 << (n)))

typedef const int_t* term;
struct cmpterm { bool operator()(term x, term y) const; };
typedef set<term, cmpterm> terms;

class table : protected dnf {
	void get(const clause&, size_t len, size_t rel, terms&) const;
	void get(const clause&, terms&) const;
public:
	const size_t ubits, rbits, arbits;
	const term q;
	const table* t;
	const bool sel;
	table(size_t ubits, size_t rbits, size_t arbits, const term q = 0, const table* t = 0);
	table(size_t ubits, size_t rbits, size_t arbits, dnf&& d, const term q = 0, const table* t = 0);
	void add(term);
	void get(terms&) const;
	table select(term) const;
	table join(const table& db, const map<term, set<terms>>& p);
};
