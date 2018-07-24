#include "macros.h"
#include <stdbool.h>

typedef struct {
	int_t r;
	size_t ar;
} term;

typedef struct {
	int_t *e;
	term *terms;
	size_t nvars, nterms, *varid;
} alt;

#define term_create(_r, _ar) ((term){ .r = _r, .ar = _ar})
#define alt_create_term(a, r, ar) alt_add_term(a, term_create(r, ar))
alt* alt_create(size_t hsz);
void alt_delete(alt* a);
void alt_add_term(alt* a, term t);
int_t alt_get_rep(alt *a, int_t v);
bool alt_add_eq(alt *a, int_t x, int_t y);
alt* alt_create_raw(int_t **b, size_t nb, size_t *sz, int_t *h, size_t nh);
alt* alt_read();
void alt_print(const alt* a);
