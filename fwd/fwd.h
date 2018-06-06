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
#include <error.h>

using namespace std;
template<typename T> using two = pair<T, T>;
typedef int32_t int_t;
typedef vector<int_t> term;
typedef set<term> clause;
typedef two<clause> rn;
typedef pair<two<term>, clause> r2;
typedef pair<term, clause> r1;
typedef int_t* tmpenv;

#define envclear(e, sz) ((tmpenv)memset((e),0,sz*sizeof(int_t)))
#define mkenv(sz) envclear(alloca(sz*sizeof(int_t)), sz)
#define dup(e, sz) env(e, &e[sz])

#define error(x) (wcerr<<(x)<<endl)
#define err_head_var_not_in_body \
error("Variables that appear on consequences must also appear in the premises")

#define debug_addxy \
	wcout << "add: " << x << " => " << y << endl
#define debug_addxyh \
	wcout << "add: " << x << ',' << y << " => " << h << endl
#define debug_unify_begin \
	wcout << "unifying: " << x << " with " << g << endl
#define debug_unify_pass \
	wcout << "passed with: " << e << endl
#define debug_sub_begin \
	wcout << "sub("<<t<<") = "
#define debug_sub_end \
	wcout << r << endl
#define debug_interpolate_begin \
	wcout << "interpolate: " << x << ',' << y
#define	debug_interpolate_end \
	wcout << " = " << r << endl

extern size_t unifications;

class fwd {
	set<rn> Rn;
	set<r2> R2;
	set<r1> R1;
	clause F;
	size_t arity = 0;

	void addrule(clause b, const clause& h);
	void add2rule(term, term, clause);
	bool add1rule(term, clause);
	void add_fact(const term&);
	void r22r1(const term&, const term&, const clause&, const term&);
	void r12r2(const term&, const clause&);
	void r12r2();
	void r22r1();
public:
	size_t operator()(clause& F, size_t& steps);
	void add(clause x, const clause& y) { addrule(x, y); }
	void add(const term& t);
};

