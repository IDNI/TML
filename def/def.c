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
#define INT_T_ERR			((int_t)-1)
#define new(x)				((x*)malloc(sizeof(x)))
#define resize(x,t,l)			((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)	(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define array_append2(a,t,b,s,l,x,y)	(++l, (((t*)resize(a, t, l))[l-1] = (x)), (((s*)resize(b, s, l))[l-1] = (y)))
#define same_term(x, y)			((x).ar == (y).ar && !memcmp((x).t, (y).t, sizeof(int_t)*((x).ar+1)))
#define str_from_id(id)			(id < 0 ? gconsts[-id-1] : gvars[id-1])
#define str_to_id(s, n)			_str_to_id(&dict, s, n)
#define clause_clear(c)			((c).terms ? free((c).terms), (c).terms=0, (c).sz=0 : 0)
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
typedef const wchar_t* ws;


struct dict_t { // used to store unique strings, map them to ids, and map to ids to general purpose void*
	const wchar_t* s;	// ptr to the string's beginning
	uint32_t h;		// hash
	int32_t id;		// given id, positive for vars, negative for consts
	size_t n;		// length of the string
	struct dict_t *l, *r;	// next in hashtable
} *dict = 0;

typedef struct { int_t *t;	size_t ar;	} term;
typedef struct { term *terms;	size_t sz;	} clause;

typedef struct dict_t dict_t;
wchar_t **gconsts = 0, **gvars = 0;
size_t gnconsts = 0, gnvars = 0;
bool clause_add_term(clause *c, const term t);

uint32_t hash(const wchar_t* s, size_t n) {
	uint32_t h = 1;
	while (n--) h *= 1 + *s * __builtin_bswap32(*s), ++s;
	return h;
}

int_t _str_to_id(dict_t **d, const wchar_t* s, size_t n) {
	uint32_t h = hash(s, n);
	if (!*d) {
		if (*s == L'?')
			return	array_append(gvars, const wchar_t*, gnvars, s),
				(*(*d = new(dict_t)) =
					(dict_t){.s=s,.h=h,.id = gnvars,.l=0,.r=0,.n=n }).id;
		else return array_append(gconsts, const wchar_t*, gnconsts, s),
			(*(*d = new(dict_t)) =
			 	(dict_t){.s=s,.h=h,.id=*s==L'~'?gnconsts:-gnconsts,.l=0,.r=0,.n=n}).id;
	}
	return	(h == (**d).h && n == (**d).n && !wmemcmp((**d).s, s, n))
		? (**d).id : _str_to_id((**d).h < h ? &(**d).l : &(**d).r, s, n);
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
	else {
		const wchar_t *s = str_from_id(n);
		while (iswalnum(*s)) putwchar(*s++);
	}
}

void term_print(const term t) {
	for (size_t n = 0; n <= t.ar; ++n) id_print(t.t[n]), putwchar(L' ');
}

clause clause_read(wchar_t **in) {
	clause c = (clause){.terms=0,.sz=0};
	if (!*in) return c;
	term t = term_read(in);
	if (!t.t) return c;
	do { clause_add_term(&c, t); } while (**in == L',' && (t = term_read(in)).t);
	if (**in == L'.') return ++*in, c;
	if (*((*in)++) != L':') perror("Term or ':' or ',' or '.' expected\n"), exit(1);
	t = term_read(in);
	if (!t.t) return clause_clear(c), c;
	do { if (*t.t = -*t.t, !clause_add_term(&c, t)) return clause_clear(c), c;
	} while (*((*in)++) == L',' && (t = term_read(in)).t);
	if (*((*in)-1) != L'.') perror("Term or ',' or '.' expected\n"), exit(1);
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
	size_t n, k = 0;
	for (n = 0; n < a.sz; ++n)
		if (*a.terms[n].t < 0)
			term_print(a.terms[n]), putwchar(L','), ++k;
	if (k == a.sz) return;
	putwchar(L':');
	for (n = 0; n < a.sz; ++n)
		if (*a.terms[n].t > 0) {
			*a.terms[n].t = -*a.terms[n].t;
			term_print(a.terms[n]), putwchar(L',');
			*a.terms[n].t = -*a.terms[n].t;
		}
	wprintf(L".\n");
}

bool clause_add_term(clause *c, const term t) {
	if (c->terms)
		for (term *x = &c->terms[0]; x != &c->terms[c->sz]; ++x)// += sizeof(term))
			if (same_term(*x, t))
				return -*t.t == *x->t;
	return array_append(c->terms, term, c->sz, t), true;
}

bool clause_compute_dst_term(const term ts, const term td, const term s, term *d) {
	d->t = realloc(d->t, sizeof(int_t) * ((d->ar = s.ar) + 1));
	for (size_t n = 1, k; n <= s.ar + 1; ++n) {
		for (k = 1; k <= td.ar + 1; ++k)
			if (td.t[k] != s.t[n] || ts.t[k] > 0) continue;
			else {
				if (td.t[k] < 0 && td.t[k] != ts.t[k]) return false;
				d->t[n] = ts.t[k];
				break;
			}
		if (k == td.ar+1) d->t[n] = td.t[n];
	}
	return true;
}

bool clause_compute_src_term(const term ts, const term td, const term s, term *d) {
	d->t = realloc(d->t, sizeof(int_t) * ((d->ar = s.ar) + 1));
	for (size_t n = 1, k; n <= s.ar + 1; ++n) {
		for (k = 1; k <= td.ar + 1; ++k)
			if (td.t[k] != s.t[n]) continue;
			else {
				if (ts.t[k] < 0 && td.t[k] < 0 && td.t[k] != ts.t[k])
					return false;
				d->t[n] = ts.t[k];
				break;
			}
		if (k == td.ar+1) d->t[n] = td.t[n];
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
		if (n != ts && clause_compute_dst_term(d.terms[td], s.terms[ts], s.terms[n], &t))
			clause_add_term(&r, t), t.t = 0;
	return r;
}

int main(int argc, char** argv) {
	setlocale(LC_CTYPE, "");
	if (argc != 4) perror(usage), exit(1);
	const size_t rlen = mbstowcs(0, argv[1], 0);
	if (rlen == (size_t)-1) perror("Unable to read the input relation symbol."), exit(1);

	wchar_t rsym[rlen];
	mbstowcs(rsym, argv[1], rlen);
	int_t r = str_to_id(rsym, rlen);

	clause c, d, *srcpos = 0, *srcneg = 0;
	size_t nsrcpos = 0, nsrcneg = 0, *srcposterm = 0, *srcnegterm = 0;
	wchar_t *all;
	for (all = file_read_text(fopen(argv[2], "r")); all;)
		if ((c = clause_read(&all)).terms) {
			bool b = false;
			for (size_t n = 0; n < c.sz; ++n)
				if (*c.terms[n].t == r)
					b = array_append2(srcpos, clause, srcposterm, size_t, nsrcpos, c, n);
				else if (-*c.terms[n].t == r)
					b = array_append2(srcneg, clause, srcnegterm, size_t, nsrcneg, c, n);
			if (!b) clause_print(c);
		}
	for (all = file_read_text(fopen(argv[3], "r")); all;)
		if ((c = clause_read(&all)).terms) {
			bool b = false;
			for (size_t n = 0; n < c.sz; ++n)
				if (*c.terms[n].t == r) {
					b = true;
					for (size_t k = 0; k < nsrcneg; ++k)
						if ((d = clause_plug(c, n, srcneg[k], srcnegterm[k])).terms)
							clause_print(d);
				} else if (-*c.terms[n].t == r) {
					b = true;
					for (size_t k = 0; k < nsrcpos; ++k)
						if ((d = clause_plug(srcpos[k], srcposterm[k], c, n)).terms)
							clause_print(d);
				}
			if (!b) clause_print(c);
		}
	return 0;
}
