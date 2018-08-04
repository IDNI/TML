// logic-programs partial-evaluator
#include <string.h>
#include <stdio.h>
#include <wctype.h>
#include <wchar.h>
#include <locale.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#define int_t			intptr_t
typedef const wchar_t* ws;
typedef struct	{ int_t *t;	size_t ar; 		} term;
typedef struct	{ term *terms;	size_t sz, nvars;	} clause;
typedef struct	{ clause *c;	size_t sz;		} lp;
typedef struct	{ int32_t id;	size_t n,l,r; ws s; uint32_t h; int_t p;}
	dict_t;
dict_t *labels = 0;
size_t nlabels = 0;
lp src, res;
int_t rel;

#define new(x)			((x*)malloc(sizeof(x)))
#define VOID			((size_t)(-1))
#define resize(x,t,l)		((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define array_append2(a,t,b,s,l,x,y)	(array_append(a, t, l, x), \
				(((s*)resize(b, s, l))[l-1] = (y)))
#define str_from_id(id)		(id < 0 ? labels[-id-1] : labels[id-1])
#define str_to_id(s, n)		_str_to_id(s, n)
#define clause_clear(c)		((clause_reset_vars(c), (c).terms ? \
				free((c).terms), (c).terms=0, (c).sz=0 : 0),c)
#define var_clear_rep(v) 	((nlabels<(size_t)v?(nlabels=v), \
				resize(labels,dict_t,v):0),labels[v-1].p=0);
#define memdup(x, t, sz)	memcpy(malloc(sizeof(t)*(sz)),x,sizeof(t)*(sz))
#define term_dup(x)		(term){.t=memdup((x).t,int_t,(x).ar+1),.ar=(x).ar}
#define lp_create()		(lp){.c=0,.sz=0}
#define clause_sort(c)		qsort(&c.terms[0], c.sz, sizeof(term), term_cmp)
#define for_all_clauses(p, x) for (clause* x=(p).c; x!=&(p).c[(p).sz]; ++x)
#define for_all_terms(c, x) for (term* x=(c).terms; x!=&(c).terms[(c).sz]; ++x)
#define for_all_args(tt, x) for (int_t* x=(tt).t+1; x!=&(tt).t[(tt).ar+1]; ++x)
#define er(x)	perror(x), exit(0)
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
#define oparen_expected "'(' expected\n"
#define entail_expected "':-' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"

uint32_t hash(ws s, size_t n) {
	uint32_t h = 1;
	while (n--) h *= 1 + *s * __builtin_bswap32(*s), ++s;
	return h;
}

int_t _str_to_id(ws s, size_t n) {
	uint32_t h = hash(s, n);
	if (!nlabels) goto create;
	dict_t *d = labels;
	int_t id;
try:	if (h == d->h && n == d->n && !wcsncmp(d->s, s, n)) return d->id;
	if (d->h < h) {
		if (d->l == VOID) { d->l = nlabels; goto create; }
		d = &labels[d->l];
		goto try;
	}
	if (d->r == VOID) { d->r = nlabels; goto create; }
	d = &labels[d->r];
	goto try;
create:	id = (*s == L'?' ? nlabels+1 : -nlabels-1);
	array_append(labels,dict_t,nlabels
		,((dict_t){.s=s,.h=h,.id=id,.l=VOID,.r=VOID,.n=n,.p=0}));
	return id;
}

int_t var_get_rep(int_t v) {
	if (v < 0) return v;
	while (labels[v-1].p > 0)
		if (v == labels[v-1].p) return (labels[v-1].p=0), v;
		else v = labels[v-1].p;
	return labels[v-1].p ? labels[v-1].p : v;
}

bool var_set_rep(int_t x, int_t y) {
	if (x < 0) {
nx:		if (y < 0 || (y = labels[y-1].p = var_get_rep(y)) < 0)
			return x == y;
		labels[y-1].p = x;
	} else if ((x = labels[x-1].p = var_get_rep(x))<0) goto nx;
	else if (y < 0) labels[x-1].p = y;
	else if ((y = labels[y-1].p = var_get_rep(y))<0) labels[x-1].p = y;
	else if (x < y) labels[y-1].p = x;
	else labels[x-1].p = y;
	return true;
}


wchar_t* str_read(int_t *r, wchar_t *in) {
	wchar_t *s = in, *t;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	if (*(t = s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = str_to_id(s, t - s);
	while (*t && iswspace(*t)) ++t;
	return t;
}

term term_read(wchar_t **in) {
	int_t x;
	term r = (term){ .t = 0, .ar = 0 };
	while (**in != L')' && (*in = str_read(&x, *in))) {
		if (!r.ar && *((*in)++) != L'(') er(oparen_expected);
		array_append(r.t, int_t, r.ar, x);
		if (!iswalnum(**in)&&**in!=L'?') break;
	}
	for (++*in; iswspace(**in); ++*in);
	return --r.ar, r;
}

int term_cmp(const void* _x, const void* _y) {
	const term *x = (const term*)_x, *y = (const term*)_y;
	return	*x->t < 0 && *y->t > 0 ? 1 : *x->t > 0 && *y->t < 0 ? -1
		: x->ar == y->ar ? memcmp(x->t, y->t, sizeof(int_t)*(x->ar+1))
		: x->ar > y->ar ? 1 : -1;
}

void id_print(int_t n) {
	if (n > 0) wprintf(L"?%d", n);
	else for (ws s = str_from_id(n).s; iswalnum(*s);) putwchar(*s++);
}

void term_print(const term t) {
	id_print(*t.t > 0 ? -*t.t : *t.t), putwchar(L'(');
	for_all_args(t, x) {
		id_print(*x);
		if (x != &t.t[t.ar]) putwchar(L' ');
	}
	putwchar(L')');
}

bool clause_add_term(clause *c, const term t) {
	for_all_args(t, x) if (*x > 0) ++c->nvars, *x = var_get_rep(*x);
	if (c->terms) for_all_terms(*c, x)
		if (!term_cmp(x, &t)) return -*t.t == *x->t;
	return array_append(c->terms, term, c->sz, t), true;
}

void clause_reset_vars(const clause c) {
	for_all_terms(c, t) for_all_args(*t, x) if (*x > 0) var_clear_rep(*x);
}

void clause_renum_vars(clause c, size_t v) {
	if (nlabels < (v+c.nvars))
		(nlabels = v+c.nvars+1), resize(labels,dict_t,v+c.nvars);
	clause_reset_vars(c);
	for_all_terms(c, t) for_all_args(*t, x)
		if (*x>0) *x=labels[*x-1].p?labels[*x-1].p:(labels[*x-1].p=++v);
}

clause clause_read(wchar_t **in) {
	clause c = (clause){.terms=0,.sz=0,.nvars=0};
	while (iswspace(**in)) ++*in;
	if (!**in) return c;
	bool neg = false;
	term t;
next:	t = term_read(in);
	if (!t.t) return c;
	if (neg) *t.t = -*t.t;
	if (!clause_add_term(&c, t)) return clause_clear(c);
	if (**in == L',' && ++*in) goto next;
	if (**in == L'.') return ++*in, c;
	if (**in == L':') {
		if (*(++*in) != L'-') er(entail_expected);
		neg = true; ++*in; goto next;
	}
	if (**in != L'.' || (neg && **in != L':')) er(sep_expected);
	clause_renum_vars(c, 0);
	return c;
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

void clause_print(const clause a) {
	bool b;
	for (size_t n = 0; n < a.sz; ++n) {
		term x = a.terms[n];
		if ((b = *x.t > 0)) (*x.t = -*x.t);
		if (term_print(x), n == a.sz - 1) putwchar(L'.');
		else if (*a.terms[n+1].t<0 && *x.t<0) fputws(L" :- ", stdout);
		else fputws(L", ", stdout);
		if (b) *x.t = -*x.t;
	}
}

int clause_cmp(const void* _x, const void* _y) {
	clause x = *(const clause*)_x, y = *(const clause*)_y;
	if (x.sz != y.sz) return x.sz > y.sz ? 1 : -1;
	for (int n = 0, r; n < (int)x.sz; ++n)
		if ((r = term_cmp(&x.terms[n], &y.terms[n]))) return r;
	return 0;
}

void lp_add_clause(clause c, bool bsrc) {
	if (!bsrc) {
		for (size_t n = 0; n < res.sz; ++n)
			if (!clause_cmp(&c, &res.c[n])) return;
		array_append(res.c, clause, res.sz, c); return;
	}
	term *x = c.terms;
	for (; x != &c.terms[c.sz]; ++x)
		if (abs(*x->t) == -rel) {
			for (size_t n = 0; n < src.sz; ++n)
				if (!clause_cmp(&c, &src.c[n]))
					return;
			array_append(src.c, clause, src.sz, c);
			return;
		}
}


clause clause_plug(clause s, const term *ps, clause d, const term *pd) {
	clause r = (clause){ .terms = 0, .sz = 0, .nvars = 0 };
	clause_renum_vars(s, d.nvars), clause_reset_vars(s), clause_reset_vars(d);
	//wprintf(L"plug "), clause_print(s), wprintf(L" into "), clause_print(d), wprintf(L" results with ");
//	const term *ps = &s.terms[ts], *pd = &d.terms[td];
	for (size_t n = 1; n <= ps->ar; ++n)
		if (!var_set_rep(ps->t[n], pd->t[n])) return clause_clear(r);
	for_all_terms(d, x) if (x != pd) clause_add_term(&r, term_dup(*x));
	for_all_terms(s, x) if (x != ps) clause_add_term(&r, term_dup(*x));
	clause_renum_vars(r, 0), clause_sort(r), clause_renum_vars(r, 0), clause_sort(r);
	clause_reset_vars(s), clause_reset_vars(d), clause_reset_vars(r);
	return r;
}

int main(int argc, char** argv) {
	setlocale(LC_CTYPE, "");
	if (argc != 4 && argc != 5) er(usage);
	bool rec = !strcmp(argv[2], "-r");
	if (rec) (argv[2] = argv[3]), argv[3] = argv[4];
	const size_t rlen = mbstowcs(0, argv[1], 0);
	if (rlen == (size_t)-1) er(err_inrel);

	clause c;
	wchar_t rsym[rlen+1], *all;
	mbstowcs(rsym, argv[1], rlen), rsym[rlen] = 0;
	rel = str_to_id(rsym, rlen);
	if (!(all = file_read_text(fopen(argv[2], "r")))) er(err_src);
	while (all && (c = clause_read(&all)).terms) lp_add_clause(c, true);
//	for_all_clauses(src, c) clause_print(*c), putwchar(L'\n');
	
	if (!(all = file_read_text(fopen(argv[3], "r")))) er(err_src);
	while ((c = clause_read(&all)).terms) {
//		clause_print(c), putwchar(L'\n');
		for_all_terms(c, x)
			if (abs(*x->t) == -rel) for (size_t n=0; n<src.sz; ++n)
				for_all_terms(src.c[n], y) if (-*y->t == *x->t)
					lp_add_clause(clause_plug(
						src.c[n], y, c, x), false);
	}
	for_all_clauses(res, c) if (c->sz) clause_print(*c), putwchar(L'\n');
	return 0;
}
