#include "pfp.h" 

map<ditem, size_t> elems, rels, vars; 
vector<ditem> delems, drels, dvars;
int_t *e;

bool ditem::operator<(const ditem& x) const { return x.n!=n ? x.n>n : (memcmp(x.s, s, n)>0); }

bool pfp(lp p, stage db) {
	map<stage, size_t> stages;
	pair<map<stage, size_t>::const_iterator, bool> it;
	for (size_t step = 0; db.size(); ++step)
		if ((it = stages.emplace(db, step)).second) db.Tp(p);
		else return it.first->second == step-1;
	return false;
}

bool stage::Tp(lp p) {
	delta add, del;
	for (rule *r = p.r; r != &p.r[p.sz]; ++r)
		if (!Tp(*r, add, del)) return false;
	return true;
}

bool unify(const term& f, const term& t) {
	if (f.size() != t.size() || f[0] != abs(t[0])) return false;
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
	for (size_t k = 0; k < t.size(); ++k) if (n!=k) r.push_back(sub(t[n]));
	return r;
}

bool stage::Tp(rule r, delta &add, delta &del) {
	for (size_t n = 1; n < r.size(); ++n)
		for (term f : at(make_pair(abs(r[n][0]), r[n].size()-1)))
			if (env_clear(r.v1, r.vn), !unify(f, r[n])) continue;
			else if (rule t = sub_chop(r, n); t.size() == 1) {
				if ((t[0][0] = -t[0][0]) > 0) {
					if (has(add, t[0])) return false;
					t[0][0] = -t[0][0], del.emplace(t[0]);
					auto it = find(get_key(t[0]));
					if (it != end()) it->second.erase(t[0]);
				} else {
					if (has(del, t[0])) return false;
					t[0][0] = -t[0][0], add.emplace(t[0]), (*this)[get_key(t[0])].emplace(t[0]);
				}
			} else if (!Tp(t, add, del)) return false;
	return true;
}

void normalize(rule &r, size_t &v) {
	for (term t : r)
		for (int_t x : t)
			if (x > 0) var_rep(x) = 0;
	for (term &t : r)
		for (int_t &x : t)
			if (x < 0) continue;
			else if (var_rep(x)) x = var_rep(x);
			else x = var_rep(x) = v++;
}

long long get_rnd() {
	static random_device d;
	static mt19937 g(d());
	static uniform_int_distribution<long long> u;
	return u(g);
}

int_t elem_get(const char *s, size_t n) {
	ditem i(s, n);
	auto it = elems.find(i);
	if (it != elems.end()) return it->second;
	i.hash = get_rnd();
	delems.push_back(i);
	return elems[i] = *s=='?' ? delems.size() : -delems.size();
}
int_t rel_get(const char *s, size_t n) {
	ditem i(s, n);
	auto it = rels.find(i);
	if (it != rels.end()) return it->second;
	i.hash = get_rnd();
	drels.push_back(i);
	return rels[i] = *s=='?' ? drels.size() : -drels.size();
}
int_t var_get(const char *s, size_t n) {
	ditem i(s, n);
	auto it = vars.find(i);
	if (it != vars.end()) return it->second;
	i.hash = get_rnd();
	dvars.push_back(i);
	return vars[i] = *s=='?' ? dvars.size() : -dvars.size();
}

long long term_hash::operator()(const term& t) const {
	long long h = 0;
	h ^= rel_get_hash(t[0]);
	for (size_t n = 1; n < t.size(); ++n)
		h ^= elem_get_hash(t[n]) << (n + 1);
	return h;
}

const wchar_t* str_read(int_t *r, const wchar_t *in, bool rel) {
	const wchar_t *s = in, *t;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	if (*(t = s) == L'?') ++t;
	bool p = *t == L'"';
	if (p) {
		++t;
		while (*(t++) != L'"') if (!*t) er(unmatched_quotes);
	} else {
		while (iswalnum(*t)) ++t;
		while (iswspace(*t)) ++t;
		if (t == s) return 0;
	}
	*r = rel ? rel_getw(s, t - s) : elem_getw(s, t - s);
	while (*t && iswspace(*t)) ++t;
	return t;
}

term term_read(const wchar_t **in) {
	int_t x;
	term r;
	bool neg = **in == L'~';
	while (**in != L')' && (*in = str_read(&x, *in, !r.size())))
		if (!r.size() && *((*in)++) != L'(') er(oparen_expected);
		else if (r.push_back(x); **in == L',') ++*in;
		else if (**in == L')') break;
		else if (r.size() != 1) er(comma_expected);
	for (++*in; iswspace(**in); ++*in);
	if (neg) r[0] = -r[0];
	return r;
}

rule rule_read(const wchar_t **in, size_t &v) {
	rule c;
	while (iswspace(**in)) ++*in;
	if (!**in) return c;
	term t = term_read(in);
	if (t.empty()) return c;
	term_for_each_arg(t, x) if (*x > 0) {
//		if (ditems.size() < (size_t)*x) ditems.resize(*x);
		var_rep(*x) = 0;
	}
	if (c.push_back(t), **in == L'.') return ++*in, c;
	if (*((*in)++) != L'i' || *((*in)++) != L'f') er(if_expected);
next:	if ((t = term_read(in)).empty()) return c;
	term_for_each_arg(t, x) if (*x > 0) var_rep(*x) = 0;
	c.push_back(t);
	if (**in != L'.') goto next;
	while (iswspace(**in)) ++*in;
	return ++*in, normalize(c, v), c;
}

lp lp_read(const wchar_t *in) {
	lp p;
	size_t v = 1;
	for (rule r; !(r = rule_read(&in, v)).empty();) array_append(p.r, rule, p.sz, r);
	return memset(e = new int_t[v], 0, v * sizeof(int_t)), p;
}

ostream& operator<<(ostream& os, const term t) {
	rel_format(t[0] > 0 ? t[0] : -t[0], os) << '(';
	cterm_for_each_arg(t, x) if (elem_format(*x, os); x != &t[t.size()]) os << ',';
	return os << ')';
}

ostream& operator<<(ostream& os, const rule t) {
	os << t[0];
	if (t.size() > 1) os << " if ";
	for (size_t n=1; n<t.size(); ++n) os<<t[n]<<(n==t.size()-1?" .":", ");
	return os;
}

int main() {
	wstring prog((istreambuf_iterator<wchar_t>(wcin)), istreambuf_iterator<wchar_t>());
	return pfp(lp_read(prog.c_str()), {});
}
