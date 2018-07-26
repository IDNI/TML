#include "def.h"
#include <unistd.h>

dict_t *dict = 0;
stack_t *stack = 0;
wchar_t **gconsts = 0, **gvars = 0;
void **vardata = 0, **srcdata = 0, **dstdata = 0;
int_t *srcs = 0;
size_t gnconsts = 0, gnvars = 0, nsrcs = 0;

uint32_t hash(const wchar_t* s, size_t n) {
	uint32_t h = 1;
	while (n--) h *= 1 + *s * __builtin_bswap32(*s), ++s;
	return h;
}

int32_t _str_to_id(dict_t **d, const wchar_t* s, size_t n, bool src) {
	uint32_t h = hash(s, n);
	size_t *sz;
	wchar_t*** a;
//	void*** data;
	if (*s == L'?') sz = &gnvars, a = &gvars;//, data = &vardata;
	else sz = &gnconsts, a = &gconsts;//, data = src ? &srcdata : &dstdata;
	if (!*d) {
		array_append(*a, const wchar_t*, *sz, s);
		if (*s == L'?') resize(vardata, void*, gnvars), vardata[gnvars-1] = 0;
		else resize(srcdata, void*, gnconsts), resize(dstdata, void*, gnconsts), srcdata[gnconsts-1]=dstdata[gnconsts-1]=0;
		(*(*d = new(dict_t)) = (dict_t){ .s=s, .h=h,
			.id = *s==L'?'?*sz:-*sz, .l=0, .r=0, .n=n });
		return (**d).id;
	} else if (h == (**d).h && n == (**d).n && !wmemcmp((**d).s, s, n))
		return (**d).id;
	else return  _str_to_id((**d).h < h ? &(**d).l : &(**d).r, s, n, src);
}

void stack_push(int_t s, int_t d, size_t a, size_t t) {
	stack_t *k = new(stack_t);
	*k = (stack_t){ .s = s, .d = d, .a = a, .t = t, .n = stack };
	stack = k;
}

bool stack_pop(int_t *s, int_t *d, size_t *a, size_t *t) {
	if (!stack) return false;
	*s = stack->s, *d = stack->d, *a = stack->a, *t = stack->t;
	stack_t *k = stack->n;
	free(stack), stack = k;
	return true;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

alt* alt_create(int_t r, size_t ar) {
	alt *a = new(alt);
	*a = (alt){ .eq = 0, .terms = 0, .nvars = ar, .nterms = 0, .hsz = ar, .r = r };
	if (ar) a->eq=calloc(ar+1, sizeof(int_t));
	return a;
}

void alt_delete(alt* a) { if (!a) return; if (a->eq) free(a->eq); if (a->terms) free(a->terms); }

void alt_add_term(alt* a, term t) {
	if (t.ar) memset(resize(a->eq, int_t, a->nvars+t.ar+1)+a->nvars+1,0,sizeof(int_t)*t.ar);
	array_append(a->terms, term, a->nterms, t), a->nvars += t.ar;
}

int_t alt_get_rep(alt *a, int_t v) {
	if (v > 0) assert((size_t)v <= a->nvars);
	if (!a->eq || v < 0 || !a->eq[v-1]) return v;
	return a->eq[v-1] = alt_get_rep(a, a->eq[v-1]);
}

bool alt_add_eq(alt *a, int_t x, int_t y) {
	x = alt_get_rep(a, x), y = alt_get_rep(a, y);
	return x==y?true:x<0?y<0?false:(a->eq[y-1]=x),true:(x>y?(a->eq[x-1]=y):(a->eq[y-1]=x)),true;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

alt* alt_add_raw(int_t *h, int_t **b, size_t nh, size_t nb, size_t *sz, bool src) {
	size_t i, j, r;
	int_t d, v;
	alt *a = alt_create(*h, nh);
	for (i = 0, v = nh; i < nb; ++i) {
		alt_create_term(a, *b[i], sz[i], v), v += sz[i];
		for (j = 1; j <= sz[i]; ++j)
			if (b[i][j] > 0)
				id_set_vardata(b[i][j], 0);
	}
	for (i = 1; i <= nh; ++i) if (h[i] > 0) id_set_vardata(h[i], 0);
	for (i = 1; i <= nh; ++i)
		if (h[i] < 0) alt_add_eq(a, i, h[i]);
		else if ((d = (int_t)id_get_vardata(h[i]))) alt_add_eq(a, i, d);
		else id_set_vardata(h[i], (void*)(i));
	for (i = 0, v = nh+1; i < nb; ++i)
		for (j = 1; j <= sz[i]; ++j, ++v)
			if (b[i][j] < 0) alt_add_eq(a, v, b[i][j]);
			else if ((d = (int_t)id_get_vardata(b[i][j]))) alt_add_eq(a, v, d);
			else id_set_vardata(b[i][j], (void*)v);
	r = def_add_alt(def_get(*h, nh, src), a);
	for (i = 0; i < a->nterms; ++i)
		for (j = 0; j < nsrcs; ++j)
			if (srcs[j] == a->terms[i].r)
				stack_push(srcs[j], *h, r, i);
	return def_get(*h, nh, src)->a[r];
}

alt* alt_plug(alt *x, const size_t t, alt *y) {
	if (!x || !y) return 0;
	wprintf(L"alt_plug x: "), alt_deflate_print(x), putwchar(L'\n');
	wprintf(L"alt_plug y: "), alt_deflate_print(y), putwchar(L'\n');
	alt *a = alt_create(x->r, x->hsz);
	size_t i, n;
	int_t j, k;
	const size_t v0 = x->terms[t].v0, hsz = y->hsz;
	for (i=0; i<x->nterms; ++i) if (i != t)	alt_add_term(a, x->terms[i]);
	for (i=0; i<y->nterms; ++i)		alt_add_term(a, y->terms[i]);
	a->nvars = x->nvars+y->nvars-hsz;
	memcpy(a->eq=realloc(a->eq, sizeof(int_t) * (a->nvars)), x->eq, sizeof(int_t) * (x->nvars));
	memset(a->eq + x->nvars, 0, sizeof(int_t) * (a->nvars-x->nvars));
	for (i = 1; i <= y->nvars; ++i) {
		j = alt_get_rep(y, i);
		if (j < 0) (n = i + x->nvars - hsz), k = j;
		else if (i == (size_t)j) continue;
		else (n = i+x->nvars-hsz), (k = j<(int_t)hsz ? (j+v0) : (j+x->nvars-hsz));
		if (!alt_add_eq(a, n, k)) return alt_delete(a), (alt*)0;
	}
	wprintf(L"alt_plug result: "), alt_deflate_print(a), putwchar(L'\n');
	return a;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

def* def_create(int_t h, size_t ar, bool src) {
	def *d = new(def);
	if (src) id_set_src(h, d);
	else id_set_dst(h, d);
	return *d = (def){ .h = term_create(h, ar, 0), .a = 0, .sz = 0 }, d;
}

def* def_get(int_t h, size_t ar, bool src) {
	def *d = src ? id_get_src(h) : id_get_dst(h);
	return d ? d : def_create(h, ar, src);
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

wchar_t* str_read(int_t *r, wchar_t *in, bool src) {
	wchar_t *s = in;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	wchar_t *t = s;
	if (*t == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = str_to_id(s, t - s, src);
	while (iswspace(*t)) ++t;
	return t;
}

int_t* term_read(size_t *sz, wchar_t **in, bool src) {
	int_t x, *t = 0;
	*sz = 0;
	while ((*in = str_read(&x, *in, src))) {
		array_append(t, int_t, *sz, x);
		if (!iswalnum(**in) && **in != L'?') return --*sz, t;
	}
	return 0;
}

void id_print(int_t n) {
	if (n > 0) {
		wprintf(L"?%d", n);
		return;
	}
	const wchar_t *s = str_from_id(n);
	while (iswalnum(*s)) putwchar(*s++);
}

void term_print(const term t, size_t v) {
	id_print(t.r);
	for (size_t n = 1; n <= t.ar; ++n) wprintf(L" ?%zu", n + v);
}

alt* alt_read(int_t **h, wchar_t **in, bool src) {
	if (!*in) return 0;
	int_t **b = 0, *t;
	size_t nb = 0, nsz = 0, *sz = 0, nh = 0, s;
	if (!(*h = term_read(&nh, in, src))) return 0;
	if (src) array_append(srcs, int_t, nsrcs, **h);
	if (**in == L'.') return ++*in, alt_add_raw(*h, 0, nh, 0, 0, src);
	else if (*((*in)++) != L':') perror("':' expected\n"), exit(1);
	while ((t = term_read(&s, in, src))) {
		if (	array_append(b, int_t*, nb, t),
			array_append(sz, size_t, nsz, s),
			**in != L',') {
				if (*((*in)++) != L'.') perror("'.' expected\n"), exit(1);
				return alt_add_raw(*h, b, nh, nb, sz, src);
			}
		else ++*in;
	}
	return 0;
}

void alt_print(alt* a) {
	term_print(term_create(a->r, a->hsz, 0), 0);
	size_t v = a->hsz;
	for (size_t n = 0; n < a->nterms; ++n)
		wprintf(L", "), term_print(a->terms[n], v), v += a->terms[n].ar;
	wprintf(L". [");
	int_t k;
	for (size_t n = 1; n <= a->nvars; ++n)
		if ((k = alt_get_rep(a, n)) > 0) { if ((size_t)k != n) wprintf(L" ?%zu = ?%lu; ", n, k); }
		else if (k < 0) wprintf(L" ?%zu = %s; ", n, str_from_id(k));
	wprintf(L"]");
}

int alt_cmp(const alt *x, const alt *y) {
	if (x->nterms != y->nterms) return x->nterms > y->nterms ? 1 : -1;
	int r = memcmp(x->terms, y->terms, sizeof(term) * x->nterms);
	if (r) return r;
	if (x->eq && y->eq) return memcmp(x->eq, y->eq, sizeof(int_t) * (x->nvars+1));
	return x->eq > y->eq ? 1 : -1;
}

size_t def_add_alt(def *d, alt *a) {
	for (size_t n = 0; n < d->sz; ++n) if (!alt_cmp(d->a[n], a)) return n;
	return array_append(d->a, alt*, d->sz, a), d->sz-1;
}

void def_print(int_t t, bool src) {
	def *d = src ? id_get_src(t) : id_get_dst(t);
	if (!d) return;
	for (size_t n = 0; n < d->sz; ++n)
		term_print(d->h, 0), wprintf(L": "), alt_print(d->a[n]), wprintf(L".\n");
}

prog prog_read(FILE *f, bool src) {
	wchar_t *all = new(wchar_t), buf[32];
	wint_t c;
	*buf = *all = 0;
	int_t *h;
	size_t n, l;
	const size_t pgnconsts = gnconsts;
	bool skip = false;
next:	for (n = l = 0; n < 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = false; break; }
		else if (c == L'#') skip = true;
		else if (c == L'\n') skip = false, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0;
		all = wcscat(resize(all, wchar_t, wcslen(all) + 32), buf);
		goto next;
	} else if (skip) goto next;
	while (all) alt_read(&h, &all, src);
	return prog_create(pgnconsts ? pgnconsts : 1, gnconsts);
}

void alt_deflate(alt *a, int_t **h, int_t ***b, size_t **sz, size_t *nb, size_t *nh) {
	if (!a) return;
	*h = arr(int_t, a->hsz+1), **h = a->r,
	*b = arr(int_t*, a->nterms), *sz = arr(size_t, a->nterms);
	*nb = a->nterms, *nh = a->hsz;
	size_t v = 0;
	for (size_t n = 0; n < a->hsz; ++n)
		(*h)[n+1] = alt_get_rep(a, ++v);
	for (size_t n = 0, m = 0; n < a->nterms; ++n, ++m) {
		(*b)[m] = arr(int_t, a->terms[n].ar + 1);
		*((*b)[m]) = a->terms[n].r;
		(*sz)[m] = a->terms[n].ar+1;
		for (size_t k = 0; k < a->terms[n].ar; ++k)
			(*b)[n][k+1] = alt_get_rep(a, ++v);
		for (size_t k = 0; k < n; ++k)
			if ((*sz)[n] == (*sz)[k] && !memcmp((*b)[n], (*b)[k], (*sz)[n] * sizeof(int_t))) {
				free((*b)[m--]);
				break;
			}
	}
}

void alt_deflate_print(alt *a) {
	if (!a) return;
	int_t *h = 0, **b = 0;
	size_t *sz = 0, nb, nh;
	alt_deflate(a, &h, &b, &sz, &nb, &nh);
	for (size_t n = 0; n <= nh; ++n) id_print(h[n]), putwchar(L' ');
	if (nb) putwchar(L':');
	for (size_t n = 0; n < nb; ++n) {
		for (size_t k = 0; k < sz[n]; ++k)
			id_print(b[n][k]), putwchar(L' ');
		if (n+1!=nb) putwchar(L',');
	}
	wprintf(L".\n");
}

void def_deflate_print(def *d) {
	for (size_t n = 0; n < d->sz; ++n) alt_deflate_print(d->a[n]);
}

void prog_print(prog p, bool src) {
	if (!p.from) ++p.from;
	for (int_t n = p.from; (size_t)n <= p.to; ++n) {
//		wprintf(L"search def of %d = %s\n", -n, str_from_id(-n));
		def *d = src ? id_get_src(-n) : id_get_dst(-n);
		if (d) def_deflate_print(d);
	}
	putwchar(L'\n');
}

void prog_plug() {
	int_t s, d;
	size_t a, t, i;
	def *ds, *dd;
	alt *ad, *r;
	while (stack_pop(&s, &d, &a, &t)) {
		ds = id_get_src(s), dd = id_get_dst(d);
		if (!(ad = dd->a[a])) continue;
		for (i = 0; i < ds->sz; ++i)
			if ((r = alt_plug(ad, t, ds->a[i])))
				array_append(dd->a, alt*, dd->sz, r);
		alt_delete(dd->a[a]), dd->a[a] = 0;
	}
}

const char usage[] = "Usage: <src filename> <dst filename>\nWill output the program after plugging src into dst.\n)";

int main(int argc, char** argv) {
	setlocale(LC_CTYPE, "");
	if (argc != 3) perror(usage), exit(1);
	prog s = prog_read(fopen(argv[1], "r"), true);
	prog d = prog_read(fopen(argv[2], "r"), false);
//	prog_print(s);
//	prog_print(d);
	prog_plug();
//	prog_print(s);
	prog_print(d, false);
	return 0;
}
