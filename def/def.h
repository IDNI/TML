#include <string.h>
#include <stdio.h>
#include <wctype.h>
#include <wchar.h>
#include <locale.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#define int_t intptr_t

struct dict_t { // used to store unique strings, map them to ids, and map to ids to general purpose void*
	const wchar_t* s;	// ptr to the string's beginning
	uint32_t h;		// hash
	int32_t id;		// given id, positive for vars, negative for consts
	size_t n;		// length of the string
	struct dict_t *l, *r;	// next in hashtable
};
typedef struct dict_t dict_t;

typedef struct {
	int_t r;		// relation id
	size_t ar, v0;		// arity and id of first var
} term;

typedef struct {
	int_t *eq;		// equality constraints
	int_t r;
	term *terms;
	size_t nvars, nterms, hsz;
} alt;

struct def {
	term h;
	alt **a;
	size_t sz;
};
typedef struct def def;

struct stack_t {
	int_t s, d;
	size_t a, t;
	struct stack_t *n;
};
typedef struct stack_t stack_t;

typedef struct {
	size_t from, to;
} prog;

uint32_t hash(const wchar_t* s, size_t n);
int32_t _str_to_id(struct dict_t **d, const wchar_t* s, size_t n, bool src);
wchar_t* str_read(int_t *r, wchar_t *in, bool);
const wchar_t* line_read(FILE *f);

alt* alt_create(int_t r, size_t ar);
void alt_delete(alt* a);
void alt_add_term(alt* a, term t);
int_t alt_get_rep(alt *a, int_t v);
bool alt_add_eq(alt *a, int_t x, int_t y);
alt* alt_add_raw(int_t *h, int_t **b, size_t nh, size_t nb, size_t *sz, bool src);
alt* alt_plug(alt *x, const size_t t, alt *y);

def* def_create(int_t h, size_t ar, bool src);
def* def_get(int_t h, size_t ar, bool src);
size_t def_add_alt(def *d, alt *a);

int_t* term_read(size_t *sz, wchar_t **in, bool);
void term_print(const term t, size_t v);
alt* alt_read(int_t **h, wchar_t **in, bool);
void alt_print(alt* a);
void alt_deflate_print(alt *a);
void alt_deflate(alt *a, int_t **h, int_t ***b, size_t **sz, size_t *nb, size_t *nh);
void def_print(int_t t, bool);

prog prog_read(FILE*, bool);
void prog_print();
void prog_plug();

#define new(x)				((x*)malloc(sizeof(x)))
#define arr(x,l)			((x*)malloc(sizeof(x)*(l)))
#define resize(x,t,l)			((t*)((x)=realloc(x,sizeof(t)*(l))))
#define memdup(x, l)			memcmp(malloc(l), x, l)
#define arrdup(x, t, n)			((t*)memdup(x, sizeof(t) * n))
#define INT_T_ERR WINT_MAX
#define array_append(a, t, l, x)	(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define def_add_alt_raw(d,b,nb,sz,h,nh)	def_add_alt(d, alt_add_raw(b, nb, sz, h, nh)
#define def_add_alt_by_rel(h, ar, a)	def_add_alt(def_get(h, ar), a)
#define alt_create_term(a, r, ar, v0)	alt_add_term(a, term_create(r, ar, v0))
#define allocat(x, y)			x=wcscat(resize(x, wchar_t, (x?wcslen(x):0))+wcslen(y)+1)), y)
#define str_from_id(id)			(id < 0 ? gconsts[-id-1] : gvars[id-1])
#define str_to_id(s, n, src)		_str_to_id(&dict, s, n, src)
#define id_set_vardata(id, data)	(vardata[id-1] = (data))
#define id_set_src(id, data)		(srcdata[-id-1] = (data))
#define id_set_dst(id, data)		(dstdata[-id-1] = (data))
#define id_get_vardata(id)		vardata[id-1]
#define id_get_src(id)			srcdata ? srcdata[-id-1] : 0
#define id_get_dst(id)			dstdata ? dstdata[-id-1] : 0
#define term_create(_r, _ar, _v0)	(term){ .r = _r, .ar = _ar, .v0 = _v0 }
#define same_term(x, y)			(((x).r == (y).r) && ((x).ar == (y).ar))
#define prog_create(f, t)		(prog){ .from = f?f:1, .to = t }

extern dict_t *dict;
extern stack_t *stack;
extern wchar_t **gconsts, **gvars;
extern void **vardata, **srcdata, **dstdata;
extern size_t gnconsts, gnvars;
