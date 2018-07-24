#include <string.h>
#include <stdio.h>
#include <wctype.h>
#include <wchar.h>
#include <locale.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>

#define new(x) malloc(sizeof(x))
#define int_t intptr_t
#define INT_T_ERR WINT_MAX
#define array_append(a, t, l, x) ((((t*)(a = realloc(a, sizeof(t)*(l+1))))[l] = x), ++l)
#define array_append_zeros(a, t, l, s) memset(((t*)realloc(a,sizeof(t)*(l+s)))+s,0,sizeof(t)*s),l+=s
#define podcmp(x, y, t) memcmp(&(x), &(y), sizeof(t))
#define def_add_alt_raw(d, b, nb, sz, h, nh) def_add_alt(d, alt_create_raw(b, nb, sz, h, nh)
#define def_add_alt_by_rel(h, ar, a) def_add_alt(def_get(h, ar), a)
#define term_create(_r, _ar) ((term){ .r = _r, .ar = _ar})
#define alt_create_term(a, r, ar) alt_add_term(a, term_create(r, ar))
#define allocat(x, y) x = wcscat(realloc(x, sizeof(wchar_t)*((x ? wcslen(x) : 0) + wcslen(y) + 1)), y)

struct dict_t {
	const wchar_t* s;
	uint32_t h;
	int32_t id;
	size_t n;
	struct dict_t *l, *r;
} *dict = 0;

wchar_t **gconsts = 0, **gvars = 0;
void **vardata = 0, **constsdata = 0;
size_t gnconsts = 0, gnvars = 0;

uint32_t hash(const wchar_t* s, size_t n) {
	uint32_t h = 1;
	while (n--) h *= 1 + *s * __builtin_bswap32(*s), ++s;
	return h;
}

int32_t _str_to_id(struct dict_t **d, const wchar_t* s, size_t n) {
	uint32_t h = hash(s, n);
	size_t *sz;
	wchar_t*** a;
	void*** data;
	if (*s == L'?') sz = &gnvars, a = &gvars, data = &vardata;
	else sz = &gnconsts, a = &gconsts, data = &constsdata;
	return	!*d ?
			array_append(*a, const wchar_t*, *sz, s),
			*data = realloc(*data, sizeof(void*)**sz),
			data[*sz-1] = 0,
			(*(*d = new(struct dict_t)) = 
				(struct dict_t){ .s=s, .h=h,
				.id = *s==L'?'?*sz:-*sz, .l=0, .r=0 }).id
			: h == (**d).h && n == (**d).n && !wmemcmp((**d).s, s, n) ? (**d).id
			: _str_to_id((**d).h < h ? &(**d).l : &(**d).r, s, n);
}

const wchar_t* str_from_id(int32_t id) {
	return id < 0 ? gconsts[-id-1] : gvars[id-1];
}

int32_t str_to_id(const wchar_t* s, size_t n) { return _str_to_id(&dict, s, n); }

void id_set_data(int32_t id, void* data) {
	if (id > 0) vardata[id] = data; else constsdata[-id] = data;
}

void* id_get_data(int32_t id) {
	return id > 0 ? vardata[id] : constsdata[-id];
}

wchar_t* str_read(int_t *r, wchar_t *in) {
	wchar_t *s = in;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	wchar_t *t = s;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = str_to_id(s, t - s);
	wchar_t *msg = malloc(sizeof(wchar_t)*(t-s+1));
	wmemcpy(msg, s, t-s+1);
	wprintf(L"%s\n", msg);
	while (iswspace(*t)) ++t;
	return t;
}

typedef struct {
	int_t r;
	size_t ar;
} term;

typedef struct {
	int_t *e;
	term *terms;
	size_t nvars, nterms, *varid;
} alt;

struct def* def_get(int_t h, size_t ar);
void def_add_alt(struct def *d, alt *a);
void def_print(int_t t);

alt* alt_create(size_t hsz) {
	alt *a = new(alt);
	*(a->varid = new(size_t)) = hsz;
	return *a = (alt){ .e = 0, .terms = 0, .nvars = hsz, .nterms = 0 }, a;
}

void alt_delete(alt* a) { if (a->e) free(a->e); if (a->terms) free(a->terms); }

void alt_add_term(alt* a, term t) {
	array_append(a->terms, term, a->nterms, t), 
	array_append(a->varid, size_t, a->nvars, a->nvars),
	array_append_zeros(a->e, int_t, a->nvars, t.ar);
}

int_t alt_get_rep(alt *a, int_t v) {
	return v < 0 || !a->e[v-1] ? v : (a->e[v-1] = alt_get_rep(a, a->e[v-1]));
}

bool alt_add_eq(alt *a, int_t x, int_t y) {
	x = alt_get_rep(a, x), y = alt_get_rep(a, y);
	return x < 0 ? y < 0 ? x == y : (a->e[y-1] = x), true : (a->e[x-1] = y), true;
}

alt* alt_create_raw(int_t **b, size_t nb, size_t *sz, int_t *h, size_t nh) {
	size_t i, j;
	int_t d, v;
	alt *a = alt_create(nh);
	for (i = 0; i < nb; ++i) {
		alt_create_term(a, *b[i], sz[i]);
		for (j = 1; j < sz[i]; ++j)
			if (b[i][j] > 0)
				id_set_data(b[i][j], 0);
	}
	for (i = 0; i < nh; ++i) if (h[i] > 0) id_set_data(h[i], 0);
	for (i = 0; i < nh; ++i)
		if (h[i] < 0) alt_add_eq(a, i+1, h[i]);
		else if ((d = (int_t)id_get_data(h[i]))) alt_add_eq(a, i+1, d);
		else id_set_data(h[i], (void*)(i+1));
	for (i = 0, v = 1; i < nb; ++i)
		for (j = 1; j < sz[i]; ++j, ++v)
			if (b[i][j] > 0) continue;
			else if ((d = (int_t)id_get_data(b[i][j]))) alt_add_eq(a, v, d);
			else id_set_data(b[i][j], (void*)v);
	return def_add_alt_by_rel(*h, nh, a), a;
}

alt* alt_plug(alt *x, size_t t, alt *y) { // replace x->terms[t] with y
	alt *a = alt_create(*x->varid);
	size_t i, v = 0, offset;
	for (i = 0; i < x->nterms; ++i) if (i != t) alt_add_term(a, x->terms[i]); 
	offset = a->nvars;
	for (i = 0; i < y->nterms; ++i) alt_add_term(a, y->terms[i]);
	memcpy(a->e, x->e, sizeof(int_t) * x->nvars); // ??
	memcpy(a->e + x->nvars, y->e, sizeof(int_t) * y->nvars);
	for (i = 0; i < y->nvars; ++i) 
		if (a->e[i + x->nvars] > 0) a->e[i + x->nvars] += x->nvars;
	for (i = x->varid[t]; i < x->terms[t].ar + x->varid[t]; ++i) alt_add_eq(a, (int_t)i, offset + v++);
	return a;
}

int_t* term_read(size_t *sz, wchar_t **in) {
	int_t x, *t = 0;
	*sz = 0;
	while ((*in = str_read(&x, *in))) {
		array_append(t, int_t, *sz, x);
		if (!iswalnum(**in)) return t;
	}
	perror("parse error\n"), exit(1);
	return t;
}


alt* alt_read(int_t **h, wchar_t **in) {
	int_t **b = 0, *t;
	size_t nb = 0, nsz = 0, *sz = 0, nh = 0, s;
	if (!(*h = term_read(&nh, in))) return 0;
	else if (**in == L'.') return alt_create_raw(0, 0, 0, *h, nh);
	else if (*((*in)++) != L':') perror("':' expected\n"), exit(1);
	while ((t = term_read(&s, in)))
		if (	array_append(b, int_t*, nb, t),
			array_append(sz, size_t, nsz, s),
			**in != L',')
			return alt_create_raw(b, nb, sz, *h, nh);
	return 0;
}

void prog_read() {
	wchar_t buf[32], *all = 0;
	int_t *h;
	while (fgetws(buf, 32, stdin)) allocat(all, buf);
	while (*all) {
		alt_read(&h, &all);
		def_print(*h);
	}
}

void term_print(const term t, size_t v) {
	const wchar_t *s = str_from_id(t.r);
	while (iswalnum(*s)) putwc(*s++, stdin);
	for (size_t n = 0; n < t.ar; ++n)
		wprintf(L" _%d", n + v);
}

void alt_print(const alt* a) {
	for (size_t n = 0; n < a->nterms; ++n) {
		term_print(a->terms[n], a->varid[n]);
		wprintf(L", ");
	}
	for (size_t n = 0; n < a->nvars; ++n)
		if (a->e[n] > 0) wprintf(L"_%d = _%d; ", n, a->e[n]);
		else if (a->e[n] < 0) wprintf(L"_%d = %d; ", n, a->e[n]);
}

struct index_t { // all alts that contain this head
	struct def *d;
	alt *a;
	size_t t;
};
typedef struct index_t index_t;

struct def {
	term h;
	alt **a;
	index_t *i;
	size_t sz, isz;
};
typedef struct def def;

def* def_create(int_t h, size_t ar) {
	def *d = new(def);
	id_set_data(h, d);
	return *d = (def){ .h = term_create(h, ar), .a = 0, .i = 0, .sz = 0, .isz = 0 }, d;
}

def* def_get(int_t h, size_t ar) {
	def *d = id_get_data(h);
	return d ? d : def_create(h, ar);
}

void def_print(int_t t) {
	def *d = id_get_data(t);
	term_print(d->h, 0);
	wprintf(L": \t");
	for (size_t n = 0; n < d->sz; ++n)
		alt_print(d->a[n]);
	wprintf(L".\n");
}


void def_add_alt(def *d, alt *a) {
	array_append(d->a, alt*, d->sz, a);
	for (size_t k = 0, n; k < a->nterms; ++k) {
		def *c = id_get_data(a->terms[k].r);
		if (!c) continue;
		const index_t i = { .d=d, .a=a, .t=k };
		for (n = 0; n < c->isz; ++n) if (!podcmp(c->i[n], i, index_t)) break;
		if (n == c->isz) array_append(c->i, index_t, c->isz, i);
	}
}

int main() {
	setlocale(LC_CTYPE, "");
	prog_read();
	return 0;
}
