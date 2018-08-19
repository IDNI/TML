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
	const char *s = 0;
	size_t n = 0;
	long long hash;
	bool operator<(const ditem& x) const;
	ditem(){}
	ditem(const char *s, size_t n) : s(s), n(n) {}
};
extern map<ditem, size_t> dict;
extern vector<ditem> ditems;

typedef vector<int_t> term;
typedef vector<term> facts;
struct term_hash { long long operator()(const term& t) const; };
typedef unordered_set<term, term_hash> delta;

struct rule : public vector<term> { size_t v1, vn; };
typedef vector<rule> lp;

struct stage : public map<pair<int_t, size_t>, set<term>> {
	bool Tp(rule r, delta &add, delta &del);
	bool Tp(lp p);
};

#define str_get(x) string(ditems[abs(x)-1].s, ditems[abs(x)-1].n)
#define str_get_hash(x) ditems[abs(x)-1].hash
#define var_rep(x) e[(x)-1]
#define has(x,y) ((x).find(y) != (x).end())
#define get_key(t) make_pair(abs((t)[0]), (t).size()-1)
#define dict_getw(ws, n) dict_get((const char*)(ws), (n) * sizeof(wchar_t))
#define id_format(n, os) (((n) > 0) ? (os << '?' << (n)) : (os << str_get(n)))
#define env_clear(from, to) memset(e+(from), 0, sizeof(int_t)*((to)-(from)))
#define er(x)	perror(x), exit(0)
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define entail_expected "':-' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
#define term_for_each_arg(t, x) for (int_t *x = &((t)[1]); x != &((t)[(t).size()]); ++x)
#define cterm_for_each_arg(t, x) for (const int_t *x = &((t)[1]); x != &((t)[(t).size()]); ++x)
