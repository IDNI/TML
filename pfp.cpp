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
typedef vector<int_t> term;
struct term_hash { long long operator()(const term& t) const; };
typedef unordered_set<term, term_hash> delta;
typedef set<term>::const_iterator iter;
typedef map<pair<int_t, size_t>, set<term>> stage;
struct stage_hash { long long operator()(const stage& t) const; };

struct rule : public vector<term> {
	set<int_t> derefs;
	size_t v1 = -1, vn = -1;
};

struct lp {
	vector<rule> r;
	set<term> q;
	stage db;
};

#define elem_get_hash(x) delems[abs(x)-1].hash
#define rel_get_hash(x) drels[abs(x)-1].hash
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
#define term_for_each_arg(t, x) for (int_t *x = &((t)[1]); x != &((t)[(t).size()]); ++x)
#define cterm_for_each_arg(t, x) for (const int_t *x = &((t)[1]); x != &((t)[(t).size()]); ++x)
#define get_key(t) make_pair(abs((t)[0]), (t).size())
#define rel_format(t, os) (((t)>0)? os << L'~' : os << wstring(drels[abs(t)-1].s, drels[abs(t)-1].n))
#define elem_format(t, os) (((t)>0)? os << L'?' << t : os << wstring(delems[-t-1].s, delems[-t-1].n))
#define min(x,y) ((x)<(y)?(x):(y))
#define max(x,y) ((x)>(y)?(x):(y))
#define env_clear(t) cterm_for_each_arg(t, x) if (*x > 0) env[*x-1] = 0
map<ditem, int_t, ditem_cmp> elems, rels, vars; 
vector<ditem> delems, drels, dvars;
int_t *env = 0;

void normalize(rule &r, size_t v) {
	r.v1 = r.vn = v;
	for (term t : r) term_for_each_arg(t, x) if (*x > 0) env[*x-1] = 0;
	for (term t : r)
		term_for_each_arg(t, x)
			if (*x > 0 && !env[*x-1]) env[*x-1] = r.vn++;
	for (term &t : r) term_for_each_arg(t, x) if (*x > 0) *x = env[*x-1];
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

long long term_hash::operator()(const term& t) const {
	long long h = 0;
	h ^= rel_get_hash(t[0]);
	for (size_t n = 1; n < t.size(); ++n) h ^= elem_get_hash(t[n]) << (n+1);
	return h;
}

long long stage_hash::operator()(const stage& t) const {
	long long h = 0;
	static term_hash th;
	for (auto x : t) for (auto y : x.second) h ^= th(y);
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

term term_read(const wchar_t **in) {
	int_t x;
	term r;
	bool neg = **in == L'~';
	if (neg) ++*in;
	while (**in != L')' && (*in = str_read(&x, *in, !r.size())))
		if (!r.size() && *((*in)++) != L'(') er(oparen_expected);
		else if (r.push_back(x); **in == L',') ++*in;
		else if (**in == L')') break;
		else if (r.size() != 1) er(comma_expected);
	for (++*in; iswspace(**in); ++*in);
	if (neg) r[0] = -r[0];
	return r;
}

rule rule_read(lp &p, const wchar_t **in) {
	rule c;
	while (iswspace(**in)) ++*in;
	if (!**in) return c;
	bool deref = false;
	if (**in == L'*') deref = true;
	term t = term_read(in);
	if (t.empty()) return c;
	if (deref) {
		p.q.emplace(t), deref = false;
		while (iswspace(**in)) ++*in;
		if (*((*in)++) != L'.') er(dot_after_q);
		return rule_read(p, in);
	}
	if (c.push_back(t), **in == L'.') 
		return p.db[get_key(t)].emplace(t), ++*in, rule_read(p, in);
	if (*((*in)++) != L'i' || *((*in)++) != L'f' || !iswspace(*((*in)++)))
		er(if_expected);
next:	deref = false;
	while (iswspace(**in)) ++*in;
	if (**in == L'*') deref = true;
	if ((t = term_read(in)).empty()) return c;
	if (deref) c.derefs.emplace(t[0]);
	if (c.push_back(t); **in != L'.') goto next;
	++*in;
	while (iswspace(**in)) ++*in;
	return c;
}

wostream& operator<<(wostream& os, const term& t) {
	rel_format(t[0], os);
	os << L'(';
	cterm_for_each_arg(t, x) {
		elem_format((*x < 0 || !env[*x-1] ? *x : env[*x-1]), os);
		if (x != &t[t.size()-1]) os << L',';
	}
	return os << L')';
}

wostream& operator<<(wostream& os, const rule& t) {
	if (os << t[0]; t.size() > 1) os << L" if ";
	for (size_t n=1; n<t.size(); ++n) os<<t[n]<<(n==t.size()-1?L" .":L", ");
	return os;
}

wostream& operator<<(wostream& os, const stage& t) {
	for (auto x : t) for (auto y : x.second) os << y << endl;
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
	for (rule r; !(r = rule_read(p, &in)).empty();) p.r.push_back(r);
	size_t v = 0, vn = 1;
	for (const rule& r : p.r) for (const term& t : r)
		cterm_for_each_arg(t, x) if (*x > 0) ++v;
	memset(env = new int_t[v], 0, v * sizeof(int_t));
	for (rule& r : p.r) normalize(r, vn), vn = r.vn, wcout << r << endl;
	return p;
}

bool unify(const term& f, const term& t) {
	if (f.size() != t.size() || f[0] != -abs(t[0])) return false;
	for (size_t n = 1; n < t.size(); ++n)
		if (t[n] < 0) { if (t[n] != f[n]) return false; }
		else if (!env[t[n]-1]) env[t[n]-1] = f[n];
		else if (env[t[n]-1] != f[n]) return false;
	return true;
}

bool set_query(stage &s, const term& q, iter& qit, iter& eit) {
	env_clear(q);
	auto it = s.find(get_key(q));
	if (it == s.end()) return false;
	return qit = it->second.begin(), eit = it->second.end(), true;
}

bool query(const term& q, iter& qit, iter& eit) {
next:	if (qit == eit) return false;
	env_clear(q);
	if (unify(*qit++, q)) return true;
	goto next;
}

bool Tp(stage &s, const rule& r, delta &add, delta &del);
bool on_match(stage &s, const rule &r, size_t n, delta &add, delta &del) {
	rule t;
	for (size_t k = 0; k < r.size(); ++k)
		if (n != k) {
			term x = r[k];
			term_for_each_arg(x, y)
				if (*y > 0 && env[*y-1]) *y = env[*y-1];
			t.push_back(move(x));
		}
	normalize(t, 1);
	//wcout << "matched " << r[n] << " remains: " << t << endl;
	memset(env + r.v1 - 1, 0, (r.vn - r.v1) * sizeof(int_t));
	if (t.size() != 1) return Tp(s, t, add, del);
	if (t[0][0] > 0) {
		if ((t[0][0] = -t[0][0]), has(add, t[0])) return false;
		del.emplace(t[0]);
	} else if (has(del, t[0])) return false;
	else add.emplace(t[0]);
	return true;
}

bool Tp(stage &s, const rule& r, delta &add, delta &del) {
	iter qit, eit;
	for (size_t n = 1; n < r.size(); ++n)
		if (memset(env + r.v1 - 1, 0, (r.vn - r.v1) * sizeof(int_t));
			set_query(s, r[n], qit, eit))
			while (query(r[n], qit, eit))
				if (!on_match(s, r,n,add,del))
					return false;
	return true;
}

bool Tp(lp &p) {
	delta add, del;
	for (const rule& r : p.r) if (!Tp(p.db, r, add, del)) return false;
	for (const term& t : add) p.db[get_key(t)].emplace(t);//, wcout << "adding " << t << endl;
	for (const term& t : del)
		if (auto it = p.db.find(get_key(t)); it != p.db.end())
			if (it->second.erase(t)){};// wcout << "erasing " << t << endl;
	return true;
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

int main() {
	setlocale(LC_ALL, "");
	return pfp(lp_read(file_read_text(stdin).c_str()));
}
