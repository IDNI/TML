// earley deduction algo by Brass&Stephan
#include <stdbool.h>
#include <stdlib.h>
#include <wchar.h>
#include <stdint.h>
#include <string.h>
#include <wctype.h>
#include <stdio.h>
#include <locale.h>

#define int_t int32_t
typedef const wchar_t* ws;
typedef struct term term; typedef struct rule rule;
typedef struct labels labels; typedef struct dict dict;
typedef struct rules rules; typedef struct facts facts;
typedef struct db db; typedef struct state state;
typedef struct dict dict; typedef struct lp lp;

struct term	{ int_t *a;	size_t ar;			};
struct rule	{ term *a;	size_t sz, nup;	rule **up;	};
struct labels	{ dict *a;	size_t sz;			};
struct rules	{ rule *t;	int_t h;	rules *r, *l;	};
struct facts	{ term *t;	int_t h;	facts *r, *l;	};
struct db	{ facts *f;	size_t sz;	term *t;	};
struct lp	{ rule *r;	size_t sz, *nv;	labels l; rules *rs;};
struct state	{ rules *act, *inact;	
		  rule *acts, *inacts;
	  	  size_t nacts, ninacts; }; 
struct dict	{ int_t id, rep, h;
		  ws s;
		  size_t n;
		  dict *r, *l; };
extern wchar_t *sout;
extern size_t outlen;
#define newline wcscat(str_resize(sout, outlen, 1),  L"\n")
#define str_resize(s, n, k) (((s) = realloc(s, sizeof(wchar_t) * (1+((n) += k)))), s)
#define out_strn(s, n) wcscat(str_resize(sout, outlen, n), s)
#define out_str(s) out_strn(s, wcslen(s))
#define out_str_f(s, a) swprintf(tmp, 128, s, a), out_str(tmp)
#define er(x)	perror(x), exit(0)
#define usage 	"Usage: <relation symbol> <src filename> <dst filename>\n"  \
		"Will output the program after plugging src into dst.\n)"
#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define entail_expected "':-' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"

#define new(x) malloc(sizeof(x))
#define resize(x,t,l)		((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define for_each_ft(t, b, e, x) for (t x = (b); x != (e); ++x)
#define for_each(t, a, sz, x) for_each_ft(t, a, &((a)[sz]) , x) 
#define for_each_o(t, a, sz, x, o) for_each_ft(t, a + o, &((a)[sz]) , x) 
#define lp_for_each_rule(p, x) for_each(const rule*, (p).r, (p).sz, x)
#define for_each_active_rule(s, x) for_each(rule*,(s).acts,(s).nacts,x)
#define for_each_inact_rule(s,x) for_each(rule*,(s).inacts,(s).ninacts,x)
#define for_each_fact(d,x) for_each(const term*, d.t, d.sz, x)
#define rule_for_each_term(r, x, o) for_each_o(term*, (r).a, (r).sz, x, o)
#define term_for_each_sym(t, x) for_each(int_t*, (t).a, (t).ar+1, x)
#define term_for_each_arg(t, x) for (int_t *x = &((t).a[1]); x != &((t).a[(t).ar+1]); ++x)
#define rule_for_each_arg(t, x, o) rule_for_each_term(t, xx, o) term_for_each_arg(*xx, x)
#define rule_for_each_sym(t, x) rule_for_each_term(t, xx, 0) term_for_each_sym(*xx, x)
#define head(x) (*(x).a)
#define afterdot(x) (x).r.a[(x).dot]
#define var_rep(p, v) ((p).l.a[(v)-1].rep)
#define rule_sub(p, x) rule_for_each_arg(x,tt,0) if(*tt>0&&var_rep(p,*tt))*tt=var_rep(p,*tt)
#define rule_reset_reps(p, r) rule_for_each_arg(r, yy, 0) if (*yy > 0) var_rep(p,*yy) = 0
#define sameterm(x,y) ((x).ar==(y).ar && !memcmp((x).a,(y).a,sizeof(int_t)*((x).ar+1)))
#define samedrule(x,y) (x).dot == (y).dot && samerule((x).r, (y).r)
#define lp_add_rule(p, r) rule_add(&(p).rs, &(p).r, &(p).sz, r)
#define vars_verify_size(p, x) if ((p).l.sz <= (size_t)(x)) resize((p).l.a, dict, x+1), \
				memset((p).l.a+(p).l.sz, 0, x+1-(p).l.sz), ((p).l.sz = x + 1)

wchar_t* file_read_text(FILE *f);
rule rule_read(lp *p, wchar_t **in);
void rule_print(lp p, const rule a, wchar_t **out, size_t *len);
int_t str_hash(ws s, size_t n);
int_t rule_hash(rule r);
int_t dict_get(labels *l, ws s, size_t n);
dict* dict_get_str(labels l, int_t n);
rule rule_normvars(lp *p, rule r);
