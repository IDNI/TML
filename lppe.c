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
#define new(x)			((x*)malloc(sizeof(x)))
#define VOID			((size_t)(-1))
#define resize(x,t,l)		((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define array_append2(a,t,b,s,l,x,y)	(array_append(a, t, l, x), \
				(((s*)resize(b, s, l))[l-1] = (y)))
#define str_from_id(id)		(id < 0 ? labels[-id-1] : labels[id-1])
#define str_to_id(s, n)		_str_to_id(s, n)
#define clause_clear(c)		((c).terms ? \
				free((c).terms), (c).terms=0, (c).sz=0 : 0)
#define string_append(x, y)	resize(x, wchar_t, wcslen(x)+wcslen(y)+1)\
				, wcscat(x, y)
#define var_clear_rep(v) \
	((nlabels<(size_t)v?(nlabels=v),resize(labels,dict_t,v):0),labels[v-1].p=0);
#define memdup(x, t, sz)	memcpy(malloc(sizeof(t)*(sz)),x,sizeof(t)*(sz))
#define term_dup(x)		(term){.t=memdup((x).t,int_t,(x).ar+1),.ar=(x).ar}
#define clause_add_new_term(c, t) clause_add_term(c, term_dup(t))
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
typedef const wchar_t* ws;

typedef struct	{ int_t *t;	size_t ar; 		} term;
typedef struct	{ term *terms;	size_t sz, nvars;	} clause;
typedef struct	{ int32_t id;	size_t n,l,r; ws s; uint32_t h; int_t p;}
	dict_t;

dict_t *labels = 0;
size_t nlabels = 0;

void clause_print(const clause a);

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
	if (*(t = s) == L'?' || *t == L'~') ++t;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = str_to_id(s, t - s);
	while (iswspace(*t)) ++t;
	return t;
}

term term_read(wchar_t **in) {
	int_t x;
	term r = (term){ .t = 0, .ar = 0 };
	while ((*in = str_read(&x, *in)))
		if (array_append(r.t,int_t,r.ar,x), !iswalnum(**in)&&**in!=L'?')
			return --r.ar, r;
	return r;
}

int term_cmp(const void* _x, const void* _y) {
	const term *x = (const term*)_x, *y = (const term*)_y;
	return x->ar == y->ar ? memcmp(x->t, y->t, sizeof(int_t)*(x->ar+1))
		: x->ar > y->ar ? 1 : -1;
}

void id_print(int_t n) {
	if (n > 0) wprintf(L"?%d", n);
	else for (ws s = str_from_id(n).s; iswalnum(*s);) putwchar(*s++);
}

void term_print(const term t) {
	id_print(*t.t > 0 ? -*t.t : *t.t), putwchar(L' ');
	for (size_t n = 1; n <= t.ar; ++n) id_print(t.t[n]), putwchar(L' ');
}

bool clause_add_term(clause *c, const term t) {
	for (int_t *x = &t.t[1]; x != &t.t[t.ar+1]; ++x)
		if (*x > 0) ++c->nvars, *x = var_get_rep(*x);
	if (c->terms)
		for (term *x = &c->terms[0]; x != &c->terms[c->sz]; ++x)
			if (!term_cmp(x, &t))
				return -*t.t == *x->t;
	return array_append(c->terms, term, c->sz, t), true;
}

void clause_reset_vars(const clause c) {
	for (const term *t = c.terms; t != &c.terms[c.sz]; ++t)
		for (const int_t *x = &t->t[1]; x != &t->t[t->ar+1]; ++x)
			if (*x > 0) var_clear_rep(*x);
}

void clause_renum_vars(clause c, size_t v) {
	if (nlabels < (v+c.nvars))
		(nlabels = v+c.nvars+1), resize(labels,dict_t,v+c.nvars);
	clause_reset_vars(c);
	for (term *t = c.terms; t != &c.terms[c.sz]; ++t)
		for (int_t *x = &t->t[1]; x != &t->t[t->ar+1]; ++x)
			if (*x < 0) continue;
			else if (labels[*x-1].p) *x = labels[*x-1].p;
			else *x = labels[*x -1].p = ++v;
}

clause clause_read(wchar_t **in) {
	clause c = (clause){.terms=0,.sz=0,.nvars=0};
	if (!*in) return c;
	bool neg = false;
	term t;
next:	t = term_read(in);
	if (!t.t) return c;
	if (neg) *t.t = -*t.t;
	if (!clause_add_term(&c, t)) return clause_clear(c), c;
	if (**in == L',' && ++*in) goto next;
	if (**in == L'.') return ++*in, c;
	if (**in == L':') { neg = true; ++*in; goto next; }
	if (*((*in)++) != (neg ? L':' : L'.'))
		perror("Term or ':' or ',' or '.' expected\n"), exit(1);
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
	if (!a.terms) return;
	size_t n, k = 0, lp = VOID, ln = VOID;
	for (n = 0; n < a.sz; ++n)
		if (*a.terms[n].t > 0) lp = n;
		else ln = n;
	if (ln != VOID)
		for (n = 0; n < a.sz; ++n)
			if (*a.terms[n].t < 0)
				term_print(a.terms[n]),
				fputws(n==ln?k==a.sz||lp==VOID?L".":L" : ":L", ",stdout), ++k;
	if (k != a.sz && ln != VOID)
		for (n = 0; n < a.sz; ++n)
			if (*a.terms[n].t > 0)
				(*a.terms[n].t = -*a.terms[n].t),
				term_print(a.terms[n]),
				fputws(n==lp?L".":L", ", stdout),
				(*a.terms[n].t = -*a.terms[n].t);
}

int clause_cmp(const void* _x, const void* _y) {
	clause x = *(const clause*)_x, y = *(const clause*)_y;
	wprintf(L"cmp ");
	clause_print(y),
	wprintf(L" to ");
	clause_print(x);
	if (x.sz != y.sz) return x.sz > y.sz ? 1 : -1;
	int r;
	for (size_t n = 0; n < x.sz; ++n)
		if (!(r = term_cmp(&x.terms[n], &y.terms[n])))
			return r;
	return 0;
}

void clause_sort(clause c) {
	qsort(&c.terms[0], c.sz, sizeof(term), term_cmp);
	for (term *b = &c.terms[1], *e = &c.terms[c.sz]; b != e;)
		if (!term_cmp(b, b-1)) memmove(b, b+1, sizeof(term)*(e-b-1));
		else ++b;

}

clause clause_plug(clause s, size_t ts, clause d, size_t td) {
	clause r = (clause){ .terms = 0, .sz = 0, .nvars = 0 };
	clause_renum_vars(s, d.nvars);
	clause_reset_vars(s), clause_reset_vars(d);
	//wprintf(L"plug "), clause_print(s), wprintf(L" into "), clause_print(d), wprintf(L" results with ");
	for (size_t n = 1; n <= s.terms[ts].ar; ++n)
		if (!var_set_rep(s.terms[ts].t[n], d.terms[td].t[n]))
			return clause_reset_vars(r), clause_clear(r), r;
	for (term* x = d.terms; x != &d.terms[d.sz]; ++x)
		if (x != &d.terms[td]) clause_add_new_term(&r, *x);
	for (term* x = s.terms; x != &s.terms[s.sz]; ++x)
		if (x != &s.terms[ts]) clause_add_new_term(&r, *x);
	clause_renum_vars(r, 0), clause_sort(r);
	clause_renum_vars(r, 0), clause_sort(r);
	clause_reset_vars(s), clause_reset_vars(d), clause_reset_vars(r);
	return r;
}

int main(int argc, char** argv) {
	setlocale(LC_CTYPE, "");
	if (argc != 4 && argc != 5) perror(usage), exit(1);
	bool rec = !strcmp(argv[2], "-r");
	if (rec) (argv[2] = argv[3]), argv[3] = argv[4];
	const size_t rlen = mbstowcs(0, argv[1], 0);
	if (rlen == (size_t)-1)
		perror("Unable to read the input relation symbol."), exit(1);

	bool b;
	clause c, d, *srcpos = 0, *srcneg = 0;
	size_t nsrcpos = 0, nsrcneg = 0, *srcposterm = 0, *srcnegterm = 0, n, k;
	wchar_t rsym[rlen+1], *all;
	mbstowcs(rsym, argv[1], rlen);
	rsym[rlen] = 0;
	int_t r = str_to_id(rsym, rlen);

	if (!(all = file_read_text(fopen(argv[2], "r"))))
		perror("Unable to read src file."), exit(1);
	while ((c = clause_read(&all)).terms) {
		if (rec) clause_print(c), putwchar(L'\n');
		for (b = false, n = 0; n < c.sz; ++n)
			if (*c.terms[n].t == r)
				array_append2(srcpos, clause, srcposterm, size_t
						, nsrcpos, c, n), b = true;
			else if (-*c.terms[n].t == r)
				array_append2(srcneg, clause, srcnegterm, size_t
						, nsrcneg, c, n), b = true;
		if (!b) clause_print(c), putwchar(L'\n');
	}

	if (!(all = file_read_text(fopen(argv[3], "r"))))
		perror("Unable to read dst file."), exit(1);
	while ((c = clause_read(&all)).terms) {
		//clause_print(c),putwchar(L'\n');
		for (b = false, n = 0; n < c.sz; ++n)
			if (*c.terms[n].t == r) {
				for (b = true, k = 0; k < nsrcneg; ++k)
					if ((d = clause_plug(c, n, srcneg[k]
						, srcnegterm[k])).terms)
						clause_print(d), putwchar(L'\n');
			} else if (-*c.terms[n].t == r)
				for (b = true, k = 0; k < nsrcpos; ++k)
					if ((d = clause_plug(srcpos[k]
						, srcposterm[k], c, n)).terms)
						clause_print(d), putwchar(L'\n');
		if (!b) clause_print(c), putwchar(L'\n');
	}
	return 0;
}
