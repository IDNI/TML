#include "dnf.h"

#define setbit(x, n) ((x) |= 1 << (n))
#define getbit(x, n) ((x) & (1 << (n)))

struct cmpterm { bool operator()(const int_t* x, const int_t* y) const; };
typedef set<const int_t*, cmpterm> terms;

class table : protected dnf {
	void get(const clause& c, size_t len, size_t rel, terms& r) const;
	void get(const clause& c, terms& r) const;
public:
	const size_t ubits, rbits, arbits;
	table(size_t ubits, size_t rbits, size_t arbits);
	void add(const int_t* t);
	void get(set<const int_t*, cmpterm>& r) const;
};
