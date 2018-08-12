// earley deduction algo by Brass&Stephan
#include <stdbool.h>
#include <stdlib.h>
#include <wchar.h>
#include <stdint.h>
#include <string.h>

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
struct db	{ facts *f;	term *t;	size_t sz;	};
struct lp	{ rule *r;	size_t sz, *nvars; labels l; 	};
struct state	{ rules *act, *inact;	
		  rule *acts, *inacts;
	  	  size_t nacts, ninacts; }; 
struct dict	{ int_t id, rep, h;
		  ws s;
		  size_t n;
		  dict *r, *l; };

#define new(x) malloc(sizeof(x))
#define resize(x,t,l)		((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define for_each_ft(t, b, e, x) for (t x = (b); x != (e); ++x)
#define for_each(t, a, sz, x) for_each_ft(t, a, &((a)[sz]) , x) 
#define lp_for_each_rule(p, x) for_each(const rule*, (p).r, (p).sz, x)
#define for_each_active_rule(s, x) for_each(rule*,(s).acts,(s).nacts,x)
#define for_each_inact_rule(s,x) for_each(rule*,(s).inacts,(s).ninacts,x)
#define for_each_fact(d,x) for_each(const term*, d.t, d.sz, x)
#define rule_for_each_term(r, x, o) for_each(term*, (r).a+o, (r).sz, x)
#define term_for_each_sym(t, x) for_each(int_t*, (t).a, (t).ar+1, x)
#define term_for_each_arg(t, x) for (int_t *x = &((t).a[1]); x != &((t).a[(t).ar+1]); ++x)
#define rule_for_each_arg(t, x, o) rule_for_each_term(t, xx, o) term_for_each_arg(*xx, x)
#define rule_for_each_sym(t, x) rule_for_each_term(t, xx, 0) term_for_each_sym(*xx, x)
#define head(x) (*(x).a)
#define afterdot(x) (x).r.a[(x).dot]
#define var_rep(p, v) ((p).l.a[(v)-1].rep)
#define rule_sub(p, x) rule_for_each_arg(x,tt,0) if(*tt>0&&var_rep(p,*tt))*tt=var_rep(p,*tt)
#define rule_reset_reps(p, r) rule_for_each_arg(r, yy, 0) if (*yy > 0) var_rep(p,*yy) = 0
#define sameterm(x,y) ((x).ar==(y).ar && !memcmp(x.a,y.a,sizeof(int_t)*((x).ar+1)))
#define samedrule(x,y) (x).dot == (y).dot && samerule((x).r, (y).r)

int_t str_hash(ws s, size_t n) {
	int_t h = 1;
	while (n--) (h *= 1 + *s * __builtin_bswap32(*s)), ++s;
	return h;
}

int_t rule_hash(rule r) {
	int_t h = 1;
	rule_for_each_sym(r, x) h *= 1 + *x * __builtin_bswap32(*x);
	return h;
}

bool samerule(rule x, rule y) {
	 if (x.sz != y.sz) return false;
	 for (size_t n = 0; n < x.sz; ++n) if (!sameterm(x.a[n], y.a[n])) return false;
	 return true;
}

rule* rule_add(rules **n, rule **a, size_t *sz, rule r) {
	int_t h = rule_hash(r);
loop:	if (!*n) {
		array_append(*a, rule, *sz, r);
		*(*n = new(rules)) = (rules){.t=&(*a)[*sz-1],.h=h,.l=0,.r=0};
		return (**n).t;
	}
	if ((**n).h == h && samerule(r, *(**n).t))
	n = (**n).h < h ? &(**n).l : &(**n).r;
	goto loop;
}

bool state_add_rule(state *s, rule r, rule *u) {
	const size_t k = s->nacts;
	rule *x = rule_add(&s->act, &s->acts, &s->nacts, r);
	array_append(x->up, rule*, x->nup, u);
	return k != s->nacts;
}

int_t dict_get(labels *l, ws s, size_t n) {
	const int_t h = str_hash(s, n);
	dict **d = &l->a;
loop:	if (!*d) {
		int_t id = *s == L'?' ? l->sz : -l->sz;
		array_append(l->a, dict, l->sz, ((dict){.id=id,.s=s,.n=n,.h=h,.l=0,.r=0}));
		return id;
	}
	if ((**d).h != h || (**d).n != n || wcsncmp(s, (**d).s, n)) {
		d = (**d).h < h ? &(**d).l : &(**d).r;
		goto loop;
	}
	return (**d).id;
}

rule rule_normvars(lp p, rule r) {
	rule_reset_reps(p, r);
	int_t v = 0;
	rule_for_each_arg(r, x, 0) if (*x > 0) var_rep(p, *x) = ++v;
	rule_sub(p, r);
	return r;
}

rule rule_dup(lp p, rule x, size_t o) {
	rule r = (rule){ .a = malloc(sizeof(term) * x.sz), .sz = o?x.sz-1:x.sz };
	size_t len = 0;
	rule_for_each_term(r, y, o) len += y->ar+1;
	int_t *t = malloc(sizeof(int_t) * len), *s = t;
	rule_for_each_term(r, y, o) term_for_each_sym(*y, z) *s++ = *z;
	for (size_t n = 0; n < r.sz; t += (r.a[n].ar=x.a[n].ar)+1) r.a[n++].a = t;
	rule_for_each_arg(x, y, o) if (*y > 0 && var_rep(p, *y)) *y = var_rep(p, *y);
	return rule_normvars(p, x);
}

int_t var_get_rep(lp p, int_t x) {
	while (x > 0 && var_rep(p, x)) x = var_rep(p, x);
	return x;
}

bool var_set_rep(lp p, int_t x, int_t y, size_t offset) {
	(x = var_get_rep(p, x)), y = var_get_rep(p, y);
	if (y > 0) y = var_get_rep(p, y + offset);
	else if (x < 0) return x == y;
	else var_rep(p, x) = y;
	return true;
}

bool rule_resolve(lp p, size_t r, rule *n, rule *res) {
	if (*head(p.r[r]).a != *n->a->a || head(p.r[r]).ar != n->a->ar) return false;
	rule_reset_reps(p, p.r[r]);
	rule_reset_reps(p, *n);
	for (size_t i = 1; i <= head(p.r[r]).ar; ++i)
		if (!var_set_rep(p, head(p.r[r]).a[i], *n->a->a, p.nvars[r]))
			return false;
	*res = rule_dup(p, p.r[r], 0);
	return true;
}

bool edb_resolve(lp p, term f, rule *n, rule *res) {
	if (*f.a != *n->a->a || f.ar !=n->a->ar) return false;
	rule_reset_reps(p, *n);
	for (size_t i = 1; i <= f.ar; ++i)
		if (!var_set_rep(p, f.a[i], n->a->a[i], 0))
			return false;
	*res = rule_dup(p, *n, 1);
	return true;
}

bool inst(state *s, const lp p, state *ss) {
	rule r;
	bool b = false;
	for (size_t n = 0; n < p.sz; ++n)
		for_each_active_rule(*s, x)
			if (rule_resolve(p, n, x, &r))
				b |= state_add_rule(ss, r, x);
	return b;
}

bool edb_reduce(lp p, state *s, const db d, state *ss) {
	rule r;
	bool b = false;
	for_each_fact(d, x)
		for_each_inact_rule(*s, y)
			if (edb_resolve(p, *x, y, &r))
				b |= state_add_rule(ss, r, y);
	return b;
}

bool idb_reduce(lp p, state *s, const db d, state *ss) {
	rule r;
	bool b = false;
	for_each_fact(d, x)
		for_each_inact_rule(*s, y)
			if (edb_resolve(p, *x, y, &r))
				b |= state_add_rule(ss, r, y);
	return b;
}
