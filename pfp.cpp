#include "pfp.h" 
#include <iostream>

map<ditem, int_t, ditem_cmp> elems, rels, vars; 
vector<ditem> delems, drels, dvars;
int_t *env = 0;
wostream& operator<<(wostream& os, const term& t);
wostream& operator<<(wostream& os, const rule& t);

bool stage::Tp(const lp &p) {
	delta add, del;
	for (const rule& r : p.r) if (!Tp(r, add, del)) return false;
	wcout << L"adding " << add.size() << " new facts: " << endl;
	for (const term& t : add) add_term(t), wcout << t << endl;
	wcout << L"erasing up to " << del.size() << " facts: " << endl;
	for (const term& t : del)
		if (auto it = find(get_key(t)); it != end())
			if (it->second.erase(t))
				wcout << t << endl;
	return true;
}

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
	for (term t : r)
		term_for_each_arg(t, x)
			if (*x > 0) var_rep(*x) = 0;
	for (term t : r)
		term_for_each_arg(t, x)
			if (*x > 0 && !var_rep(*x)) var_rep(*x) = r.vn++;
	for (term &t : r)
		term_for_each_arg(t, x)
			if (*x > 0) *x = var_rep(*x);
}

bool unify(const term& f, const term& t) {
//	wcout << "unify " << f << " with " << t << endl;
	if (f.size() != t.size() || f[0] != -abs(t[0])) return false;
	for (size_t n = 1; n < t.size(); ++n)
		if (t[n] < 0) { if (t[n] != f[n]) return false; }
		else if (!var_rep(t[n])) var_rep(t[n]) = f[n];
		else if (var_rep(t[n]) != f[n]) return false;
//	wcout << "success" << endl;
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
	normalize(r, 1);
	return r;
}
bool stage::on_match(const rule &r, size_t n, delta &add, delta &del) {
	if (rule t = sub_chop(r, n); t.size() == 1) {
		if (t[0][0] > 0) {
			t[0][0] = -t[0][0];
			if (has(add, t[0])) return false;
			del.emplace(t[0]);
		} else if (has(del, t[0])) return false;
		else add.emplace(t[0]);
	} else return Tp(t, add, del);
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
	auto it = elems.find(i);
	if (it != elems.end()) return it->second;
	return	i.hash = get_rnd(), delems.push_back(i),
		elems[i] = *s=='?' ? delems.size() : -delems.size();
}

int_t rel_get(const wchar_t *s, size_t n) {
	ditem i(s, n);
	auto it = rels.find(i);
	if (it != rels.end())
		return it->second;
	return (i.hash = get_rnd()), drels.push_back(i), rels[i] = -drels.size();
}

int_t var_get(const wchar_t *s, size_t n) {
	ditem i(s, n);
//	if (dvars.size()<=n)dvars.resize(n),e=(int_t*)realloc(e,sizeof(int_t)*n);
	auto it = vars.find(i);
	if (it != vars.end()) return it->second;
	i.hash = get_rnd();
	dvars.push_back(i);
	return vars[i] = dvars.size();
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
//	term_for_each_arg(r, x) if (*x > 0) var_rep(*x) = 0;
	return r;
}

rule rule_read(lp &p, const wchar_t **in) {
	rule c;
	while (iswspace(**in)) ++*in;
	if (!**in) return c;
	bool deref = false;
	set<int_t> dset;
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
		return p.db.add_term(t), ++*in, rule_read(p, in);
	if (*((*in)++) != L'i' || *((*in)++) != L'f' || !iswspace(*((*in)++)))
		er(if_expected);
next:	deref = false;
	while (iswspace(**in)) ++*in;
	if (**in == L'*') deref = true;
	if ((t = term_read(in)).empty()) goto ret;
	if (deref) c.derefs.emplace(t[0]);
	c.push_back(t);
	if (**in != L'.') goto next;
	while (iswspace(**in)) ++*in;
	++*in;
ret:	set<int_t> vs;
	for (const term& t : c)
		cterm_for_each_arg(t, x)
			if (*x > 0) vs.emplace(*x);
	if (vs.size()) c.vn = c.v1 + vs.size();
	else c.v1 = c.vn = 0;
	return c;
}

wostream& operator<<(wostream& os, const term& t) {
	rel_format(t[0], os);
	os << L'(';
	cterm_for_each_arg(t, x)
		if (elem_format(*x, os); x != &t[t.size()-1])
			os << L',';
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
	for (rule r; !(r = rule_read(p, &in)).empty();)
		p.r.push_back(r);
	size_t v = 0;
	for (const rule& r : p.r) for (const term& t : r)
		cterm_for_each_arg(t, x) if (*x > 0) ++v;
	memset(env = new int_t[v], 0, v * sizeof(int_t));
	size_t vn = 1;
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

int main() {
	setlocale(LC_ALL, "");
	wstring prog((istreambuf_iterator<wchar_t>(wcin)),istreambuf_iterator<wchar_t>());
	return pfp(lp_read(prog.c_str()));
}
