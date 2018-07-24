#include "alt.h"
#include "dict.h"
#include <string.h>
#include <stdio.h>
#include <wctype.h>

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
	return v < 0 || !a->e[v] ? v : (a->e[v] = alt_get_rep(a, a->e[v]));
}

bool alt_add_eq(alt *a, int_t x, int_t y) {
	x = alt_get_rep(a, x), y = alt_get_rep(a, y);
	return x < 0 ? y < 0 ? x == y : (a->e[y] = x), true : (a->e[x] = y), true;
}

alt* alt_create_raw(int_t **b, size_t nb, size_t *sz, int_t *h, size_t nh) {
	size_t i, j;
	int_t d, v;
	alt *a = alt_create(nh);
	for (i = 0; i < nb; ++i) {
		alt_create_term(a, *b[i], sz[i]);
		for (j = 1; j < sz[i]; ++j)
			id_set_data(b[i][j], (void*)(int_t)-1);
	}
	for (i = 0; i < nh; ++i) id_set_data(h[i], (void*)(int_t)-1);
	for (i = 0; i < nh; ++i)
		if (-1 == (d = (int_t)id_get_data(h[i]))) id_set_data(h[i], (void*)i);
		else alt_add_eq(a, i, d);
	for (i = v = 0; i < nb; ++i)
		for (j = 1; j < sz[i]; ++j, ++v)
			if (-1 == (d = (int_t)id_get_data(b[i][j]))) id_set_data(b[i][j], (void*)v);
			else alt_add_eq(a, v, d);
	return a;
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

//alt* alt_create_raw(int_t **b, size_t nb, size_t *sz, int_t *h, size_t nh);

int_t* term_read(size_t *sz, wint_t *c) {
	int_t x, *t = 0;
	*sz = 0;
	while (INT_T_ERR != (*c = str_read(&x))) {
		array_append(t, int_t, *sz, x);
		if (!iswalnum(*c)) return t;
	}
	perror("parse error\n"), exit(-1);
	return t;
}

alt* alt_read() {
	int_t **b = 0, *h = 0, *t;
	size_t nb = 0, *sz = 0, nh = 0, s;
	wint_t c;
	if (!(h = term_read(&nh, &c))) return 0;
	else if (c == L'.') return alt_create_raw(0, 0, 0, h, nh);
	while ((t = term_read(&s, &c)))
		if (	array_append(b, int_t*, nb, t),
			array_append(sz, size_t, nb, s),
			c != L',')
			return alt_create_raw(b, nb, sz, h, nh);
	return 0;
}
