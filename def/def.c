#include "alt.h"
#include "dict.h"
#include <string.h>

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

#define def_add_alt_raw(d, b, nb, sz, h, nh) def_add_alt(d, alt_create_raw(b, nb, sz, h, nh)

// now plug algo
// first we only need a plug algo that plugs a single occurence in a body.
// then we repeat till fixed point.
// so no need to calc all options in one pass.
// in other words we'll have intermediary defs.

// first assume (and build) a list per rel that contains *all* terms per alt that contain it.
// store it in a def's head
/*
void def_plug(int_t h, int_t b) {
	def *dh = (def*)id_get_data(h), *db = (def*)id_get_data(b), *dr = def_create(dh->h.r, dh->h.ar);
	for (size_t n = 0; n < h->sz; ++n) {
		alt *a = dh->a[n];
		for (size_t k = 0; k < a->nterms; ++k)
			if (a->terms[k] != dh->h) ;//def_add_alt(dr, a);
			else for (size_t i = 0; i < db->sz; ++i) {
				def_add_alt(dr, alt_sub(a, k, db->terms[k]));
			}
		
	}
}*/
