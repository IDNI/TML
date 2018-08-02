#include <string.h>
#include <stdio.h>
#include <wctype.h>
#include <wchar.h>
#include <locale.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#define int_t				intptr_t
#define new(x)				((x*)malloc(sizeof(x)))
#define VOID				((size_t)(-1))
#define resize(x,t,l)			((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)	(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define array_append2(a,t,b,s,l,x,y)	(array_append(a, t, l, x), (((s*)resize(b, s, l))[l-1] = (y)))
#define same_term(x, y)			((x).ar == (y).ar && !memcmp((x).t, (y).t, sizeof(int_t)*((x).ar+1)))
#define str_from_id(id)			(id < 0 ? labels[-id-1].s : labels[id-1].s)
#define str_to_id(s, n)			_str_to_id(s, n)
#define clause_clear(c)			((c).terms ? free((c).terms), (c).terms=0, (c).sz=0 : 0)
#define string_append(x, y)		resize(x, wchar_t, wcslen(x)+wcslen(y)+1), wcscat(x, y)
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
typedef const wchar_t* ws;

typedef struct	{ int_t *t;	size_t ar;			 } term;
typedef struct	{ term *terms;	size_t sz;			 } clause;
typedef struct	{ int32_t id;	size_t n, l, r; ws s; uint32_t h;} dict_t;

size_t nlabels = 0;
dict_t dict = {.id=0, .n=0,.r=0,.l=0,.h=0,.s=0};
dict_t *labels = 0;

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
	array_append(labels,dict_t,nlabels,((dict_t){.s=s,.h=h,.id=id,.l=VOID,.r=VOID,.n=n }));
	return id;
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
		if (array_append(r.t, int_t, r.ar, x), !iswalnum(**in) && **in != L'?')
			return --r.ar, r;
	return r;
}

void id_print(int_t n) {
	if (n > 0) wprintf(L"?%d", n);
	else for (ws s = str_from_id(n); iswalnum(*s);) putwchar(*s++);
}

void term_print(const term t) {
	id_print(*t.t > 0 ? -*t.t : *t.t), putwchar(L' ');
	for (size_t n = 1; n <= t.ar; ++n) id_print(t.t[n]), putwchar(L' ');
}

bool clause_add_term(clause *c, const term t) {
	if (c->terms)
		for (term *x = &c->terms[0]; x != &c->terms[c->sz]; ++x)// += sizeof(term))
			if (same_term(*x, t))
				return -*t.t == *x->t;
	return array_append(c->terms, term, c->sz, t), true;
}

clause clause_read(wchar_t **in) {
	clause c = (clause){.terms=0,.sz=0};
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
	if (*((*in)++) != (neg ? L':' : L'.')) perror("Term or ':' or ',' or '.' expected\n"), exit(1);
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

void clause_print(clause a) {
	if (!a.terms) return;
	size_t n, k = 0, lp, ln;
	for (n = 0; n < a.sz; ++n)
		if (*a.terms[n].t > 0) lp = n;
		else ln = n;
	for (n = 0; n < a.sz; ++n)
		if (*a.terms[n].t < 0)
			term_print(a.terms[n]), wprintf(n == ln ? k == a.sz ? L".\n" : L" : " : L", "), ++k;
	if (k != a.sz)
		for (n = 0; n < a.sz; ++n)
			if (*a.terms[n].t > 0)
				(*a.terms[n].t = -*a.terms[n].t),
				term_print(a.terms[n]), wprintf(n == lp ? L".\n" : L", "),
				(*a.terms[n].t = -*a.terms[n].t);
}

bool clause_compute_dst_term(const term ts, const term td, const term s, term *d) {
	d->t = realloc(d->t, sizeof(int_t) * ((d->ar = s.ar) + 1));
	for (size_t n = 1, k; n <= s.ar; ++n) {
		for (k = 1; k <= td.ar; ++k)
			if (td.t[k] != s.t[n] || ts.t[k] > 0) continue;
			else if (td.t[k] < 0 && td.t[k] != ts.t[k]) return false;
			else { 	d->t[n] = ts.t[k];
				break; }
		if (k == td.ar + 1) d->t[n] = s.t[n];
	}
	*d->t = *s.t;
	return true;
}

bool clause_compute_src_term(const term ts, const term td, const term s, term *d) {
	d->t = realloc(d->t, sizeof(int_t) * ((d->ar = s.ar) + 1));
	*d->t = *s.t;
	for (size_t n = 1, k; n <= s.ar; ++n) {
		for (k = 1; k <= td.ar; ++k)
			if (td.t[k] != s.t[n]) continue;
			else if (ts.t[k] < 0 && td.t[k] < 0 && td.t[k] != ts.t[k]) return false;
			else {	d->t[n] = ts.t[k];
				break; }
		if (k == td.ar + 1) d->t[n] = s.t[n];
	}
	return true;
}

clause clause_plug(clause s, size_t ts, clause d, size_t td) {
	clause r = (clause){ .terms = 0, .sz = 0 };
	term t = (term) { .t = 0, .ar = 0 };
	for (size_t n = 0; n < d.sz; ++n)
		if (n != td && clause_compute_dst_term(s.terms[ts], d.terms[td], d.terms[n], &t))
			clause_add_term(&r, t), t.t = 0;
	for (size_t n = 0; n < s.sz; ++n)
		if (n != ts && clause_compute_src_term(d.terms[td], s.terms[ts], s.terms[n], &t))
			clause_add_term(&r, t), t.t = 0;
	return r;
}

int main(int argc, char** argv) {
	setlocale(LC_CTYPE, "");
	if (argc != 4) perror(usage), exit(1);
	const size_t rlen = mbstowcs(0, argv[1], 0);
	if (rlen == (size_t)-1) perror("Unable to read the input relation symbol."), exit(1);

	bool b;
	clause c, d, *srcpos = 0, *srcneg = 0;
	size_t nsrcpos = 0, nsrcneg = 0, *srcposterm = 0, *srcnegterm = 0, n, k;
	wchar_t rsym[rlen+1], *all;
	mbstowcs(rsym, argv[1], rlen);
	rsym[rlen] = 0;
	int_t r = str_to_id(rsym, rlen);

	if (!(all = file_read_text(fopen(argv[2], "r")))) perror("Unable to read src file."), exit(1);
	while ((c = clause_read(&all)).terms) {
		clause_print(c);
		for (b = false, n = 0; n < c.sz; ++n)
			if (*c.terms[n].t == r)
				array_append2(srcpos, clause, srcposterm, size_t, nsrcpos, c, n), b = true;
			else if (-*c.terms[n].t == r)
				array_append2(srcneg, clause, srcnegterm, size_t, nsrcneg, c, n), b = true;
		if (!b) clause_print(c);
	}

	if (!(all = file_read_text(fopen(argv[3], "r")))) perror("Unable to read dst file."), exit(1);
	while ((c = clause_read(&all)).terms) {
		for (b = false, n = 0; n < c.sz; ++n)
			if (*c.terms[n].t == r) {
				for (b = true, k = 0; k < nsrcneg; ++k)
					if ((d = clause_plug(c, n, srcneg[k], srcnegterm[k])).terms)
						clause_print(d);
			} else if (-*c.terms[n].t == r)
				for (b = true, k = 0; k < nsrcpos; ++k)
					if ((d = clause_plug(srcpos[k], srcposterm[k], c, n)).terms)
						clause_print(d);
		if (!b) clause_print(c);
	}
	return 0;
}
