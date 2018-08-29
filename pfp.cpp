#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include <cstdint>
#include <string>
#include <cstring>
#include <iostream>
#include <random>
#include <sstream>
#include <climits>
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
struct term_hash { long long operator()(const int_t* t) const; };
struct same_term { long long operator()(const int_t* x, const int_t *y) const; };
typedef unordered_set<const int_t*, term_hash, same_term> delta;
typedef delta::const_iterator iter;
typedef map<pair<int_t, size_t>, unordered_set<const int_t*, term_hash, same_term>> stage;
struct stage_hash { long long operator()(const stage& t) const; };

struct rule {
	vector<int_t> t;
	vector<size_t> pos;
	vector<bool> neg;
	set<int_t> derefs, ex;
	size_t v1 = -1, vn = -1;
	void add_lit(const int_t*, bool);
	void add_lit(const rule& r, size_t n);
};

struct lp {
	vector<rule> r;
	set<int_t*> q;
	stage db;
};

#define has(x,y) ((x).find(y) != (x).end())
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
#define term_for_each_arg(t, x) for (int_t *x = &((t)[2]); x != &((t)[(t)[0]+1]); ++x)
#define cterm_for_each_arg(t, x) for (const int_t *x = &((t)[2]); x != &((t)[(t)[0]+1]); ++x)
#define rule_for_each_term(r, x) for (int_t *x = &(r).t[0]; *x; x += *x+1)
#define crule_for_each_term(r, x) for (const int_t *x = &(r).t[0]; *x; x += *x+1)
#define get_key(t) make_pair((t)[1], (t)[0])
#define rel_format(t, os) (os << wstring(drels[-t-1].s, drels[-t-1].n))
#define elem_format(t, os) (((t)>0)? os << L'?' << t : os << wstring(delems[-t-1].s, delems[-t-1].n))
#define min(x,y) ((x)<(y)?(x):(y))
#define max(x,y) ((x)>(y)?(x):(y))
#define env_clear(t) cterm_for_each_arg(t, x) if (*x > 0) env[*x-1] = 0
#define resize(x,t,l)		((t*)((x)=(t*)realloc(x,sizeof(t)*(l))))
#define term_append(a, x)	((int_t*)resize(a, int_t, *a))[(*a)-1] = (x)
#define rule_clear(r) ((r).t.clear(), (r).pos.clear(), (r).neg.clear(), (r).derefs.clear(), (r).ex.clear(), ((r).v1 = (r).vn = -1))
map<ditem, int_t, ditem_cmp> elems, rels, vars; 
vector<ditem> delems, drels, dvars;
int_t *env = 0;

void normalize(rule &r, size_t v) {
	r.v1 = r.vn = v;
	crule_for_each_term(r,t) cterm_for_each_arg(t,x) if (*x>0) env[*x - 1]=0;
	crule_for_each_term(r,t) cterm_for_each_arg(t,x) if (*x>0&&!env[*x-1]) env[*x-1]=r.vn++;
	 rule_for_each_term(r,t)  term_for_each_arg(t,x) if (*x>0) *x=env[*x-1];
	crule_for_each_term(r,t) cterm_for_each_arg(t,x) if (*x>0) env[*x-1]=0;
}

long long get_rnd() {
	static random_device d;
	static mt19937 g(d());
	static uniform_int_distribution<long long> u;
	return u(g);
}

int_t elem_get(const wchar_t *s, size_t n) {
	ditem i(s, n);
	if (auto it = elems.find(i); it != elems.end()) return it->second;
	return	i.hash = get_rnd(), delems.push_back(i),
		elems[i] = *s=='?' ? delems.size() : -delems.size();
}

int_t rel_get(const wchar_t *s, size_t n) {
	ditem i(s, n);
	if (auto it = rels.find(i); it != rels.end()) return it->second;
	return (i.hash=get_rnd()),drels.push_back(i),rels[i]=-drels.size();
}

int_t var_get(const wchar_t *s, size_t n) {
	ditem i(s, n);
	if (auto it = vars.find(i); it != vars.end()) return it->second;
	return i.hash = get_rnd(), dvars.push_back(i), vars[i] = dvars.size();
}

long long same_term::operator()(const int_t* x, const int_t *y) const {
	return !memcmp(x, y, sizeof(int_t)*(*x+1));
}

long long term_hash::operator()(const int_t* t) const {
	long long h = 0;
	h ^= drels[-t[1]-1].hash - 127;
	for (size_t n = 2; n < (size_t)*t; ++n) h ^= delems[abs(t[n])-1].hash << (n+1);
	return h;
}

long long stage_hash::operator()(const stage& t) const {
	long long h = 0;
	static term_hash th;
	for (auto x : t) for (auto y : x.second) h ^= th(&y[0]);
	return h;
}

const wchar_t* str_read(int_t *r, const wchar_t *in, bool rel) {
	const wchar_t *s = in, *t;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	if (*(t = s) == L'?') ++t;
	bool p = *t == L'"';
	if (p) {
		for (++t; *(t++) != L'"';) if (!*t) er(unmatched_quotes);
	} else {
		while (iswalnum(*t)) ++t;
		while (iswspace(*t)) ++t;
		if (t == s) return 0;
	}
	*r = rel ? rel_get(s, t - s) : elem_get(s, t - s);
	while (*t && iswspace(*t)) ++t;
	return t;
}

int_t* term_read(const wchar_t **in) {
	int_t x, *r = (int_t*)malloc(sizeof(int_t));
	*r = 0;
	bool neg = **in == L'~';
	if (neg) ++*in;
	while (**in != L')' && (*in = str_read(&x, *in, !*r)))
		if (!*r && *((*in)++) != L'(') er(oparen_expected);
		else if (r=(int_t*)realloc(r, (*r+2)*sizeof(int_t)), r[++*r]=x;
			**in == L',') ++*in;
		else if (**in == L')') break;
		else if (*r != 1) er(comma_expected);
	for (++*in; iswspace(**in); ++*in);
	if (neg) r[1] = -r[1];
	return r;
}

rule* rule_read(lp &p, const wchar_t **in) {
	while (iswspace(**in)) ++*in;
	if (!**in) return 0;
	bool deref = false, neg;
	if (**in == L'*') deref = true;
	int_t* t = term_read(in);
	if (!*t) return free(t), nullptr;
	if (deref) {
		p.q.emplace(t), deref = false;
		while (iswspace(**in)) ++*in;
		if (*((*in)++) != L'.') er(dot_after_q);
		return rule_read(p, in);
	}
	rule *c = new rule;
	if ((neg = t[1] > 0)) t[1] = -t[1];
	if (c->add_lit(t, neg), **in == L'.') 
		return p.db[get_key(t)].emplace(&c->t[c->pos.size()-1]), free(t), ++*in, rule_read(p, in);
	if (*((*in)++) != L'i' || *((*in)++) != L'f' || !iswspace(*((*in)++)))
		er(if_expected);
next:	deref = false;
	while (iswspace(**in)) ++*in;
	if (**in == L'*') deref = true;
	if (!*(t = term_read(in))) return free(t), c;
	if ((neg = t[1] > 0)) t[1] = -t[1];
	if (deref) c->derefs.emplace(t[1]);
	if (c->add_lit(t, neg), free(t); **in != L'.') goto next;
	++*in;
	while (iswspace(**in)) ++*in;
	return c;
}

wostream& operator<<(wostream& os, const int_t* t) {
	wstringstream ss;
	rel_format(t[1], ss);
	ss << L'(';
	cterm_for_each_arg(t, x) {
		if (env) elem_format((*x < 0 || !env[*x-1] ? *x : env[*x-1]), ss);
		else elem_format(*x, ss);
		wstring s = ss.str();
		if (x != &t[*t]) ss << L',';
	}
	wstring s = ss.str();
	os << s;
	return os << L')';
}

wostream& operator<<(wostream& os, const rule& t) {
	if (os << &t.t[0]; t.pos.size() > 1) os << L" if ";
	for (size_t n = 1; n < t.pos.size(); ++n)
		os<<&t.t[t.pos[n]]<<(n==t.pos.size()-1?L" .":L", ");
	return os;
}

wostream& operator<<(wostream& os, const stage& t) {
	for (auto x : t) for (auto y : x.second) os << &y[0] << endl;
	return os;
}

wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n < 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = 0; break; }
		else if (c == L'#') skip = 1;
		else if (c == L'\r' || c == L'\n') skip = 0, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0, ss << buf;
		goto next;
	} else if (skip) goto next;
	return ss.str();
}

lp lp_read(const wchar_t *in) {
	lp p;
	for (rule *r; (r = rule_read(p, &in)) && !r->t.empty();)
		p.r.push_back(*r), wcout << *r << endl;
	size_t v = 0, vn = 1;
	for (const rule& r : p.r) for (const int_t& t : r.t) if (t > 0) ++v;
	memset(env = new int_t[v], 0, v * sizeof(int_t));
	for (rule& r : p.r)
		normalize(r, vn), vn = r.vn, wcout << r << endl;
	return p;
}

void rule::add_lit(const int_t *l, bool _neg) {
	neg.push_back(_neg);
	if (!t.size()) t.push_back(0);
	pos.push_back(t.size()-1);
	t.insert(t.end()-1, l, l + *l + 1);
}

void rule::add_lit(const rule& r, size_t n) {
	size_t l = r.t[r.pos[n]] + 1;
	if (!t.size()) t.push_back(0);
	pos.push_back(t.size()-1), neg.push_back(r.neg[n]);
	t.insert(t.end()-1, &r.t[r.pos[n]], &r.t[r.pos[n] + l]);
	for (int_t *x = &t[t.size() - l]; x != &t[t.size()]; ++x)
		if (*x > 0 && env[*x - 1])
			*x = env[*x - 1];
}

bool unify(const int_t* f, const int_t* t) {
//	wcout << L"unify " << t << L" vs " << f << endl;
	env_clear(t);
	size_t n = *t - 1;
	if (*f++ != *t++ || *f++ != *t++) return false;
	while (n--)
		if (*t < 0) { if (*t != *f) return false; }
		else if (!env[*t-1]) env[*t++-1] = *f++;
		else if (env[*t-1] != *f) return false;
//	wcout << L"success" << endl;
	return true;
}

bool set_query(stage &s, const int_t *q, iter& qit, iter& eit) {
	if (auto it = s.find(get_key(q)); it == s.end()) return false;
	else return qit = it->second.begin(), eit = it->second.end(), true;
}

bool query(const int_t *q, iter& qit, iter& eit) {
	while (qit != eit) if (unify(*qit++, q)) return true;
	return false;
}
#define dup(x) ((int_t*)memcpy(malloc(sizeof(int_t)*((*x)+1)), x, sizeof(int_t)*((*x)+1)))
bool Tp(stage&, const rule&, rule*, delta&, delta&);
bool on_match(stage &s, const rule &r, rule *t, size_t n, delta& add, delta& del) {
	rule_clear(*t);
	for (size_t k = 0; k < r.pos.size(); ++k)
		if (n != k) t->add_lit(r, k);
	normalize(*t, 1), memset(env + r.v1 - 1, 0, (r.vn - r.v1)*sizeof(int_t));
	rule *tr = t + 1;
	return	t->pos.size() != 1 ? Tp(s, *t, tr, add, del) :
		(!t->neg[0] || !has(add, &t->t[0])) && (t->neg[0] || !has(del, &t->t[0]))
		&& ((t->neg[0] ? del : add).emplace(dup(&t->t[0])), true);
}

bool Tp(stage &s, const rule& r, rule *t, delta& add, delta& del) {
	iter qit, eit;
	for (size_t n = 1; n < r.pos.size(); ++n)
		if (r.neg[n]) {
		} else if (set_query(s, &r.t[r.pos[n]], qit, eit))
			while (query(&r.t[r.pos[n]], qit, eit))
				if (!on_match(s, r, t, n, add, del))
					return false;
	return true;
}

bool Tp(lp &p) {
	delta add, del;
	size_t b = 0;
	for (const rule& r : p.r) b = max(b, r.pos.size());
	rule *tr = new rule[b];
	for (const rule& r : p.r) if (!Tp(p.db, r, tr, add, del)) return delete[] tr, false;
	for (const int_t* t : add) p.db[get_key(t)].emplace(t);//, wcout << "adding " << t << endl;
	for (const int_t* t : del)
		if (auto it = p.db.find(get_key(t)); it != p.db.end())
			if (it->second.erase(t)){} // wcout << "erasing " << t << endl;
	return delete[] tr, true;
}

bool pfp(lp p) {
	unordered_map<stage, size_t, stage_hash> stages;
	pair<unordered_map<stage, size_t, stage_hash>::const_iterator, bool> it;
	for (size_t step = 0; p.db.size(); ++step)
		if ((it = stages.emplace(p.db, step)).second) {
			wcout << L"stage " << step << L": " << endl << p.db;
			if (!Tp(p)) wcout << "stopping on contradiction" << endl;
		} else {
			wcout << L"same as stage " << it.first->second << endl;
			return it.first->second == step-1;
		}
	return false;
}

int _main() {
	setlocale(LC_ALL, "");
	return pfp(lp_read(file_read_text(stdin).c_str()));
}
