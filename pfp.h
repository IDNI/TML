#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cstdint>
#include <string>
#include <cstring>
#include <cwctype>
#include <iostream>
#include <random>
using namespace std;

typedef int32_t int_t;

struct ditem {
	const wchar_t *s = 0;
	size_t n = 0;
	long long hash;
	ditem(){}
	ditem(const wchar_t *s, size_t n) : s(s), n(n) {}
};
struct ditem_cmp {
	bool operator()(const ditem& x, const ditem& y) const {
		return x.n!=y.n ? x.n<y.n : (memcmp(x.s, y.s, y.n*sizeof(wchar_t))<0);
	}
};

typedef vector<int_t> term;
struct term_hash { long long operator()(const term& t) const; };
typedef unordered_set<term, term_hash> delta;

struct rule : public vector<term> {
	set<int_t> derefs;
	size_t v1, vn;
};

#define get_key(t) make_pair(abs((t)[0]), (t).size())

struct stage : public map<pair<int_t, size_t>, set<term>> {
	bool Tp(const rule& r, delta &add, delta &del);
	bool Tp(const struct lp& p);
	bool add_term(const term& t) { return (*this)[get_key(t)].emplace(t).second; }
};

struct lp {
	vector<rule> r;
	set<term> q;
	stage db;
};

void rel_format(int_t n, wostream& os);
void elem_format(int_t n, wostream& os);

#define s2ws(s) wc2c.from_bytes(s)
#define rel_get_str(x) s2ws(string(drels[abs(x)-1].s, drels[abs(x)-1].n))
#define elem_get_str(x) s2ws(string(delems[abs(x)-1].s, delems[abs(x)-1].n))
#define elem_get_hash(x) delems[abs(x)-1].hash
#define rel_get_hash(x) drels[abs(x)-1].hash
#define has(x,y) ((x).find(y) != (x).end())
//#define elem_getw(ws, n) elem_get((const char*)(ws), (n) * sizeof(wchar_t))
//#define rel_getw(ws, n) rel_get((const char*)(ws), (n) * sizeof(wchar_t))
#define env_clear(from, to) memset(env+(from)-1, 0, sizeof(int_t)*((to)-(from)))
#define _resize(x,t,l)		(((x)=(t*)realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)_resize(a, t, l))[l-1] = (x)))
#define er(x)	perror(x), exit(0)
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define dot_after_q "expected '.' after query (dereferenced head).\n"
#define if_expected "'if' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
#define term_for_each_arg(t, x) for (int_t *x = &((t)[1]); x != &((t)[(t).size()]); ++x)
#define cterm_for_each_arg(t, x) for (const int_t *x = &((t)[1]); x != &((t)[(t).size()]); ++x)
#define var_rep(n) env[n-1]
