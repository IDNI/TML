#include <vector>
#include <set>
#include <map>
#include <iostream>
#include <cstring>
#include <alloca.h>
#include <algorithm>

typedef int32_t int_t;
typedef std::vector<int_t> term;
typedef std::set<term> terms;
typedef std::vector<term> clause;
typedef int_t* env;
std::ostream& operator<<(std::ostream&, const env&);
std::ostream& operator<<(std::ostream&, const term&);
std::ostream& operator<<(std::ostream&, const terms&);

#ifdef NDEBUG
#define DEBUG(x)
#define DBGOUT(x)
#else
#define DEBUG(x) x
#define DBGOUT(x) cout << x << endl
#endif

class fwd {
	std::vector<clause> negs, poss;
	size_t *numvars;
	std::vector<std::vector<std::set<env>>> matches;
	std::map<std::pair<size_t, size_t>,
		std::set<std::pair<size_t, size_t>>> p2n;
	void sub_negs(size_t, size_t, const term&);
	void sub_poss(size_t, size_t, terms&, const env&);
	void cache(size_t n, size_t k, size_t i, size_t j);
	void print_clauses();
	void print_matches();
public:
	fwd(std::vector<clause> negs, std::vector<clause> poss);
	void operator()(terms&);
	~fwd() { delete[] numvars; }
};
