// earley deduction algo by Brass&Stephan
#include <stdbool.h>
#include <stdlib.h>
#include <wchar.h>
#include <stdint.h>
#include <string.h>
#include <wctype.h>
#include <stdio.h>
#include <locale.h>

#define int_t int32_t
typedef const wchar_t* ws;
typedef struct term term; typedef struct rule rule;
typedef struct labels labels; typedef struct dict dict;
typedef struct rules rules; typedef struct facts facts;
typedef struct db db; typedef struct state state;
typedef struct dict dict; typedef struct lp lp;

struct term	{ int_t *a;	size_t ar;			};
struct rule	{ term *a;	size_t sz, nup;	rule **up;	};
struct labels	{ dict *a;	size_t sz;			};
struct rules	{ rule *t;	int_t h;	rules *r, *l;	};
struct facts	{ term *t;	int_t h;	facts *r, *l;	};
struct db	{ facts *f;	size_t sz;	term *t;	};
struct lp	{ rule *r;	size_t sz, *nv;	labels l; rules *rs;};
struct state	{ rules *act, *inact;	
		  rule *acts, *inacts;
	  	  size_t nacts, ninacts; }; 
struct dict	{ int_t id, rep, h;
		  ws s;
		  size_t n;
		  dict *r, *l; };
wchar_t *sout = 0;
size_t outlen = 0;
#define newline wcscat(str_resize(sout, outlen, 1),  L"\n")
#define str_resize(s, n, k) (((s) = realloc(s, sizeof(wchar_t) * (1+(n += k)))), s)
#define out_strn(s, n) wcscat(str_resize(sout, outlen, n), s)
#define out_str(s) out_strn(s, wcslen(s))
#define out_str_f(s, a) swprintf(tmp, 128, s, a), out_str(tmp)
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

#define new(x) malloc(sizeof(x))
#define resize(x,t,l)		((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define for_each_ft(t, b, e, x) for (t x = (b); x != (e); ++x)
#define for_each(t, a, sz, x) for_each_ft(t, a, &((a)[sz]) , x) 
#define lp_for_each_rule(p, x) for_each(const rule*, (p).r, (p).sz, x)
#define for_each_active_rule(s, x) for_each(rule*,(s).acts,(s).nacts,x)
#define for_each_inact_rule(s,x) for_each(rule*,(s).inacts,(s).ninacts,x)
#define for_each_fact(d,x) for_each(const term*, d.t, d.sz, x)
#define rule_for_each_term(r, x, o) for_each(term*, (r).a+o, (r).sz, x)
#define term_for_each_sym(t, x) for_each(int_t*, (t).a, (t).ar+1, x)
#define term_for_each_arg(t, x) for (int_t *x = &((t).a[1]); x != &((t).a[(t).ar+1]); ++x)
#define rule_for_each_arg(t, x, o) rule_for_each_term(t, xx, o) term_for_each_arg(*xx, x)
#define rule_for_each_sym(t, x) rule_for_each_term(t, xx, 0) term_for_each_sym(*xx, x)
#define head(x) (*(x).a)
#define afterdot(x) (x).r.a[(x).dot]
#define var_rep(p, v) ((p).l.a[(v)-1].rep)
#define rule_sub(p, x) rule_for_each_arg(x,tt,0) if(*tt>0&&var_rep(p,*tt))*tt=var_rep(p,*tt)
#define rule_reset_reps(p, r) rule_for_each_arg(r, yy, 0) if (*yy > 0) var_rep(p,*yy) = 0
#define sameterm(x,y) ((x).ar==(y).ar && !memcmp((x).a,(y).a,sizeof(int_t)*((x).ar+1)))
#define samedrule(x,y) (x).dot == (y).dot && samerule((x).r, (y).r)
#define lp_add_rule(p, r) rule_add(&(p).rs, &(p).r, &(p).sz, r)

int_t str_hash(ws s, size_t n) {
	int_t h = 1;
	while (n--) (h *= 1 + *s * __builtin_bswap32(*s)), ++s;
	return h;
}

int_t rule_hash(rule r) {
	int_t h = 1;
	rule_for_each_sym(r, x) h *= 1 + *x * __builtin_bswap32(*x);
	return h;
}

bool samerule(rule x, rule y) {
	 if (x.sz != y.sz) return false;
	 for (size_t n = 0; n < x.sz; ++n) if (!sameterm(x.a[n], y.a[n])) return false;
	 return true;
}

rule* rule_add(rules **n, rule **a, size_t *sz, rule r) {
	int_t h = rule_hash(r);
loop:	if (!*n) {
		array_append(*a, rule, *sz, r);
		*(*n = new(rules)) = (rules){.t=&(*a)[*sz-1],.h=h,.l=0,.r=0};
		return (**n).t;
	}
	if ((**n).h == h && samerule(r, *(**n).t))
	n = (**n).h < h ? &(**n).l : &(**n).r;
	goto loop;
}

bool state_add_rule(state *s, rule r, rule *u) {
	const size_t k = s->nacts;
	rule *x = rule_add(&s->act, &s->acts, &s->nacts, r);
	array_append(x->up, rule*, x->nup, u);
	return k != s->nacts;
}

int_t dict_get(labels *l, ws s, size_t n) {
	const int_t h = str_hash(s, n);
	dict **d = &l->a;
loop:	if (!*d) {
		int_t id = *s == L'?' ? l->sz : -l->sz;
		array_append(l->a, dict, l->sz, ((dict){.id=id,.s=s,.n=n,.h=h,.l=0,.r=0}));
		return id;
	}
	if ((**d).h != h || (**d).n != n || wcsncmp(s, (**d).s, n)) {
		d = (**d).h < h ? &(**d).l : &(**d).r;
		goto loop;
	}
	return (**d).id;
}

dict* dict_get_str(labels l, int_t n) { return n > 0 ? &l.a[n-1] : &l.a[-n-1]; }

rule rule_normvars(lp p, rule r) {
	rule_reset_reps(p, r);
	int_t v = 0;
	rule_for_each_arg(r, x, 0) if (*x > 0) var_rep(p, *x) = ++v;
	rule_sub(p, r);
	return r;
}

rule rule_dup(lp p, rule x, size_t o) {
	rule r = (rule){ .a = malloc(sizeof(term) * x.sz), .sz = o?x.sz-1:x.sz };
	size_t len = 0;
	rule_for_each_term(r, y, o) len += y->ar+1;
	int_t *t = malloc(sizeof(int_t) * len), *s = t;
	rule_for_each_term(r, y, o) term_for_each_sym(*y, z) *s++ = *z;
	for (size_t n = 0; n < r.sz; t += (r.a[n].ar=x.a[n].ar)+1) r.a[n++].a = t;
	rule_for_each_arg(x, y, o) if (*y > 0 && var_rep(p, *y)) *y = var_rep(p, *y);
	return rule_normvars(p, x);
}

int_t var_get_rep(lp p, int_t x) {
	while (x > 0 && var_rep(p, x)) x = var_rep(p, x);
	return x;
}

bool var_set_rep(lp p, int_t x, int_t y, size_t offset) {
	(x = var_get_rep(p, x)), y = var_get_rep(p, y);
	if (y > 0) y = var_get_rep(p, y + offset);
	else if (x < 0) return x == y;
	else var_rep(p, x) = y;
	return true;
}

bool rule_resolve(lp p, size_t r, rule *n, rule *res) {
	if (*head(p.r[r]).a != *n->a->a || head(p.r[r]).ar != n->a->ar) return false;
	rule_reset_reps(p, p.r[r]);
	rule_reset_reps(p, *n);
	for (size_t i = 1; i <= head(p.r[r]).ar; ++i)
		if (!var_set_rep(p, head(p.r[r]).a[i], *n->a->a, p.nv[r]))
			return false;
	*res = rule_dup(p, p.r[r], 0);
	return true;
}

bool edb_resolve(lp p, term f, rule *n, rule *res) {
	if (*f.a != *n->a->a || f.ar !=n->a->ar) return false;
	rule_reset_reps(p, *n);
	for (size_t i = 1; i <= f.ar; ++i)
		if (!var_set_rep(p, f.a[i], n->a->a[i], 0))
			return false;
	*res = rule_dup(p, *n, 1);
	return true;
}

bool inst(state *s, const lp p, state *ss) {
	rule r;
	bool b = false;
	for (size_t n = 0; n < p.sz; ++n)
		for_each_active_rule(*s, x)
			if (rule_resolve(p, n, x, &r))
				b |= state_add_rule(ss, r, x);
	return b;
}

bool edb_reduce(lp p, state *s, const db d, state *ss) {
	rule r;
	bool b = false;
	for_each_fact(d, x)
		for_each_inact_rule(*s, y)
			if (edb_resolve(p, *x, y, &r))
				b |= state_add_rule(ss, r, y);
	return b;
}

bool idb_reduce(lp p, state *s, const db d, state *ss) {
	rule r;
	bool b = false;
	for_each_fact(d, x)
		for_each_inact_rule(*s, y)
			if (edb_resolve(p, *x, y, &r))
				b |= state_add_rule(ss, r, y);
	return b;
}

wchar_t* str_read(lp p, int_t *r, wchar_t *in) {
	wchar_t *s = in, *t;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	if (*(t = s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	while (iswspace(*t)) ++t;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = dict_get(&p.l, s, t - s);
	while (*t && iswspace(*t)) ++t;
	return t;
}

term term_read(lp p, wchar_t **in) {
	int_t x;
	term r = (term){ .a = 0, .ar = 0 };
	while (**in != L')' && (*in = str_read(p, &x, *in))) {
		if (!r.ar && *((*in)++) != L'(') er(oparen_expected);
		array_append(r.a, int_t, r.ar, x);
		if (**in == L',') ++*in;
		else if (**in == L')') break;
		else if (r.ar != 1) er(comma_expected);
	}
	for (++*in; iswspace(**in); ++*in);
	return --r.ar, r;
}

wchar_t tmp[128];
void id_print(lp p, int_t n, wchar_t **out, size_t *len) {
	if (n > 0) out_str_f(L"?%d", n);
	else {
		ws s = dict_get_str(p.l, n)->s;
		size_t l = dict_get_str(p.l, n)->n;
		if (l >= 8 && !wcsncmp(s,L"default:", 8)) (s += 8), l -= 8;
		wcsncat(*out = str_resize(*out, *len, l), s, l);
	}
}

void term_print(lp p, const term t, wchar_t **out, size_t *len) {
	id_print(p, *t.a > 0 ? -*t.a : *t.a, out, len);
	wcscat(str_resize(*out, *len, 1), L"(");
	term_for_each_arg(t, x) {
		id_print(p, *x, out, len);
		if (x != &t.a[t.ar])// putwchar(L',');
			wcscat(str_resize(*out, *len, 1), L",");
	}
	wcscat(str_resize(*out, *len, 1), L")");
}

void rule_add_term(rule *c, const term t) {
//	term_for_each_arg(t, x) if (*x > 0) ++c->nvars, *x = var_get_rep(*x);
	rule_for_each_term(*c, x, 1)
		if (sameterm(*x, t))
			return;
	array_append(c->a, term, c->sz, t);
}

rule rule_read(lp p, wchar_t **in) {
	rule c = (rule){.a=0,.sz=0};
	while (iswspace(**in)) ++*in;
	if (!**in) return c;
	term t = term_read(p, in);
	if (!t.a) return c;
	term_for_each_arg(t, x) if (*x > 0) var_rep(p, *x) = 0;
	if (**in == L'.') return ++*in, c;
	if (*((*in)++) != L':' || *((*in)++) != L'-') er(entail_expected);
next:	if (!(t = term_read(p, in)).a) return c;
	term_for_each_arg(t, x) if (*x > 0) var_rep(p, *x) = 0;
	rule_add_term(&c, t);
	if (**in != L'.') goto next;
	rule_normvars(p, c);
	return ++*in,  c;
}

wchar_t* file_read_text(FILE *f) {
	wchar_t *all = new(wchar_t), buf[32];
	wint_t c;
	*buf = *all = 0;
	size_t n, l;
	bool skip = false;
next:	for (n = l = 0; n < 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = false; break; }
		else if (c == L'#') skip = true;
		else if (c == L'\r' || c == L'\n') skip = false, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0;
		all = wcscat(resize(all, wchar_t, wcslen(all) + 32), buf);
		goto next;
	} else if (skip) goto next;
	return all;
}

void rule_print(lp p, const rule a, wchar_t **out, size_t *len) {
	term_print(p, *a.a, out, len);
	if (a.sz > 1) wcscat(str_resize(*out, *len, 4), L" :- ");
	for (size_t n = 1; n < a.sz; ++n)
		term_print(p, a.a[n], out, len),
		wcscat(str_resize(*out, *len, 1), n == a.sz - 1 ? L" ." : L", ");
}

int main(int argc, char** argv) {
	sout = new(wchar_t);
	*sout = 0;

	setlocale(LC_CTYPE, "");
	if (argc != 3 && argc != 4) er(usage);
	rule r;
	wchar_t *all;
	lp p = (lp){.r=0,.sz=0,.nv=0,.l=(labels){.a=0,.sz=0}};
	if (!(all = file_read_text(fopen(argv[2], "r")))) er(err_src);
	while (all && (r = rule_read(p, &all)).a)
		lp_add_rule(p, r), rule_print(p, r, &sout, &outlen);
}
