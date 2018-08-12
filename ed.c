// earley deduction algo by Brass&Stephan
#include <stdbool.h>
#include <stdlib.h>
#include <wchar.h>
#include <stdint.h>
#include <string.h>

#define int_t int32_t
typedef const wchar_t* ws;
#define declare_2struct(a,b,c,d,n) struct n { a b; c d; }; typedef struct n n
#define declare_vector(t, sz, n) declare_2struct(t, *a, size_t, sz, n)
declare_vector(int_t, ar, term);
declare_vector(term, sz, rule);
declare_2struct(rule, r, size_t, dot, drule);
declare_2struct(drule, r, struct node, *up, node);
typedef struct nodes nodes;
struct nodes {
	node n;
	int32_t h;
	struct nodes *r, *l;
};
struct state {
	nodes *act, *inact;
	node *acts, inacts;
	size_t nacts, ninacts;
};
typedef struct state state;

declare_vector(struct dict, sz, labels);

struct dict {
	int_t id, rep;
	ws s;
	size_t n;
	uint32_t h;
	struct dict *r, *l;
};
typedef struct dict dict;
typedef struct {
	rule *r;
	size_t sz, *nvars;
	labels l;
} lp;

#define new(x) malloc(sizeof(x))
#define resize(x,t,l)		((t*)((x)=realloc(x,sizeof(t)*(l))))
#define array_append(a, t, l, x)(++l, (((t*)resize(a, t, l))[l-1] = (x)))
#define for_each_ft(t, b, e, x) for (t x = (b); x != (e); ++x)
#define for_each(t, a, sz, x) for_each_ft(t, a, &((a)[sz]) , x) 
#define lp_for_each_rule(p, x) for_each(const rule*, (p).r, (p).sz, x)
#define for_each_active_node(s, x) for_each(node*,(s).acts,(s).nacts,x)
#define for_each_inact_node(s,x)for_each(node*,(s).inact.a,(s).inact.sz,x)
#define rule_for_each_term(r, x) for_each(term*, (r).a, (r).sz, x)
#define term_for_each_sym(t, x) for_each(int_t*, (t).a, (t).ar+1, x)
#define term_for_each_arg(t, x) for (int_t *x = &((t).a[1]); x != &((t).a[(t).ar+1]); ++x)
#define rule_for_each_arg(t, x) rule_for_each_term(t, xx) term_for_each_arg(*xx, x)
#define rule_for_each_sym(t, x) rule_for_each_term(t, xx) term_for_each_sym(*xx, x)
#define head(x) (*(x).a)
#define afterdot(x) (x).r.a[(x).dot]
#define var_rep(p, v) ((p).l.a[(v)-1].rep)
#define rule_sub(p, x) rule_for_each_arg(x,tt) if(*tt>0&&var_rep(p,*tt))*tt=var_rep(p,*tt)
#define rule_reset_reps(p, r) rule_for_each_arg(r, yy) if (*yy > 0) var_rep(p,*yy) = 0
#define node_get_dotted(x) ((x).r.r.a[(x).r.dot])
#define sameterm(x,y) ((x).ar==(y).ar && !memcmp(x.a,y.a,sizeof(int_t)*((x).ar+1)))
#define samedrule(x,y) (x).dot == (y).dot && samerule((x).r, (y).r)

uint32_t str_hash(ws s, size_t n) {
	uint32_t h = 1;
	while (n--) (h *= 1 + *s * __builtin_bswap32(*s)), ++s;
	return h;
}

uint32_t drule_hash(drule r) {
	uint32_t h = 1;
	rule_for_each_sym(r.r, x) h *= 1 + *x * __builtin_bswap32(*x) + r.dot;
	return h;
}

bool samerule(rule x, rule y) {
	 if (x.sz != y.sz) return false;
	 for (size_t n = 0; n < x.sz; ++n) if (!sameterm(x.a[n], y.a[n])) return false;
	 return true;
}

node* node_add(nodes **n, node **a, size_t *sz, drule r) {
	int_t h = drule_hash(r);
loop:	if (!*n) {
		*(*n = new(nodes)) = (nodes){.n=(node){.r=r,.up=0},.h=h,.l=0,.r=0};
		array_append(*a, node, *sz, (**n).n);
		return &((**n).n);
	}
	if ((**n).h == h && samedrule(r, (**n).n.r))
	n = (**n).h < h ? &(**n).l : &(**n).r;
	goto loop;
}

bool state_add_rule(state *s, drule r, node *u) {
	const size_t k = s->nacts;
	node_add(&s->act, &s->acts, &s->nacts, r)->up = u;
	return k != s->nacts;
}

int_t dict_get(labels *l, ws s, size_t n) {
	const uint32_t h = str_hash(s, n);
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
	rule_for_each_arg(r, x) if (*x > 0) var_rep(p, *x) = ++v;
	rule_sub(p, r);
	return r;
}

rule rule_dup(lp p, rule x) {
	rule r = (rule){ .a = malloc(sizeof(term) * x.sz), .sz = x.sz };
	size_t len = 0;
	rule_for_each_term(r, y) len += y->ar+1;
	int_t *t = malloc(sizeof(int_t) * len), *s = t;
	rule_for_each_term(r, y) term_for_each_sym(*y, z) *s++ = *z;
	for (size_t n = 0; n < r.sz; t += (r.a[n].ar=x.a[n].ar)+1) r.a[n++].a = t;
	rule_for_each_arg(x, y) if (*y > 0 && var_rep(p, *y)) *y = var_rep(p, *y);
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

bool resolve(lp p, size_t r, node *n, rule *res) {
	if (*head(p.r[r]).a != *node_get_dotted(*n).a || head(p.r[r]).ar != node_get_dotted(*n).ar) return false;
	rule_reset_reps(p, p.r[r]);
	rule_reset_reps(p, n->r.r);
	for (size_t i = 1; i <= head(p.r[r]).ar; ++i)
		if (!var_set_rep(p, head(p.r[r]).a[i], afterdot(n->r).a[i], p.nvars[r]))
			return false;
	*res = rule_dup(p, p.r[r]);
	return true;
}

void inst(state *s, const lp p, state *ss) {
	rule r;
	for (size_t n = 0; n < p.sz; ++n)
		for_each_active_node(*s, x)
			if (resolve(p, n, x, &r))
				state_add_rule(ss, (drule){.r=r,.dot=0}, x);
}
