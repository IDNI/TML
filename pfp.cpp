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
#include <sstream>
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
	size_t v1 = -1, vn = -1;
};

struct stage : public map<pair<int_t, size_t>, set<term>> {
	bool Tp(const rule& r, delta &add, delta &del);
	bool on_match(const rule &r, size_t n, delta &add, delta &del);
	bool Tp(const struct lp& p);
};

struct lp {
	vector<rule> r;
	set<term> q;
	stage db;
};

void rel_format(int_t n, wostream& os);
void elem_format(int_t n, wostream& os);

#define elem_get_hash(x) delems[abs(x)-1].hash
#define rel_get_hash(x) drels[abs(x)-1].hash
#define has(x,y) ((x).find(y) != (x).end())
#define env_clear(from, to) memset(env+(from)-1, 0, sizeof(int_t)*((to)-(from)))
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
#define get_key(t) make_pair(abs((t)[0]), (t).size())

map<ditem, int_t, ditem_cmp> elems, rels, vars; 
vector<ditem> delems, drels, dvars;
int_t *env = 0;
wostream& operator<<(wostream& os, const term& t);
wostream& operator<<(wostream& os, const rule& t);

void rel_format(int_t n, wostream& os) {
	if (n > 0) os << L'~';
	os << wstring(drels[abs(n)-1].s, drels[abs(n)-1].n);
}

void elem_format(int_t n, wostream& os) {
	if (n > 0) os << L'?' << n;
	else os << wstring(delems[-n-1].s, delems[-n-1].n);
}

void normalize(rule &r, size_t v) {
	r.v1 = r.vn = v;
	for (term t : r) term_for_each_arg(t, x) if (*x > 0) var_rep(*x) = 0;
	for (term t : r)
		term_for_each_arg(t, x)
			if (*x > 0 && !var_rep(*x)) var_rep(*x) = r.vn++;
	for (term &t : r) term_for_each_arg(t, x) if (*x > 0) *x = var_rep(*x);
}

bool unify(const term& f, const term& t) {
	if (f.size() != t.size() || f[0] != -abs(t[0])) return false;
	for (size_t n = 1; n < t.size(); ++n)
		if (t[n] < 0) { if (t[n] != f[n]) return false; }
		else if (!var_rep(t[n])) var_rep(t[n]) = f[n];
		else if (var_rep(t[n]) != f[n]) return false;
	return true;
}

term sub(const term& t) {
	term r = t;
	term_for_each_arg(r, x) if (*x > 0 && var_rep(*x)) *x = var_rep(*x);
	return r;
}

rule sub_chop(const rule& t, size_t n) {
	rule r;
	for (size_t k = 0; k < t.size(); ++k) if (n!=k) r.push_back(sub(t[k]));
	return normalize(r, 1), r;
}

bool stage::Tp(const lp &p) {
	delta add, del;
	for (const rule& r : p.r) if (!Tp(r, add, del)) return false;
	wcout << L"adding " << add.size() << " new facts: " << endl;
	for (const term& t : add) (*this)[get_key(t)].emplace(t), wcout << t << endl;
	wcout << L"erasing up to " << del.size() << " facts: " << endl;
	for (const term& t : del)
		if (auto it = find(get_key(t)); it != end())
			if (it->second.erase(t))
				wcout << t << endl;
	return true;
}

bool stage::on_match(const rule &r, size_t n, delta &add, delta &del) {
	rule t = sub_chop(r, n);
	if (t.size() != 1) return Tp(t, add, del);
	if (t[0][0] > 0) {
		if ((t[0][0] = -t[0][0]), has(add, t[0])) return false;
		del.emplace(t[0]);
	} else if (has(del, t[0])) return false;
	else add.emplace(t[0]);
	return true;
}

bool stage::Tp(const rule& r, delta &add, delta &del) {
	for (size_t n = 1; n < r.size(); ++n) {
		auto it = find(get_key(r[n]));
		if (r[n][0] > 0) {
			if (it == end()) {
				if (!on_match(r, n, add, del)) return false;
				continue;
			}
			bool b = false;
			for (term f : it->second)
				if (env_clear(r.v1, r.vn), b = unify(f, r[n]))
					break;
			if (!b&&(env_clear(r.v1, r.vn), !on_match(r,n,add,del)))
				return false;
		} else if (it == end()) continue;
		else for (term f : it->second) {
			if (env_clear(r.v1, r.vn), !unify(f, r[n])) continue;
			else if (!on_match(r, n, add, del)) return false;
		}
	}
	return true;
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

const wchar_t* str_read(int_t *r, const wchar_t *in, bool rel) {
	const wchar_t *s = in, *t;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	if (*(t = s) == L'?') ++t;
	bool p = *t == L'"';
	if (p) {
		for (++t; *(t++) != L'"';)
			if (!*t)
				er(unmatched_quotes);
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
	cterm_for_each_arg(t,x)if(elem_format(*x,os);x!=&t[t.size()-1])os<<L',';
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

bool pfp(lp p) {
	map<stage, size_t> stages;
	pair<map<stage, size_t>::const_iterator, bool> it;
	for (size_t step = 0; p.db.size(); ++step)
		if ((it = stages.emplace(p.db, step)).second)
			(wcout << L"stage " << step << L": " << endl << p.db),
			p.db.Tp(p);
		else return it.first->second == step-1;
	return false;
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

int main() {
	setlocale(LC_ALL, "");
	return pfp(lp_read(file_read_text(stdin).c_str()));
}
