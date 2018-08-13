#include "ed.h"

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
	if ((**n).h == h && samerule(r, *(**n).t)) return (**n).t;
	n = (**n).h < h ? &(**n).l : &(**n).r;
	goto loop;
}

bool state_add_rule(state *s, rule r, rule *u) {
	const size_t k = s->nacts;
	rule *x = rule_add(&s->act, &s->acts, &s->nacts, r);
	array_append(x->up, rule*, x->nup, u);
	return k != s->nacts;
}

rule rule_normvars(lp *p, rule r) {
	rule_reset_reps(*p, r);
	int_t v = 0;
	rule_for_each_arg(r, x, 0) 
		if (*x > 0) {
			vars_verify_size(*p, *x);
			vars_verify_size(*p, v+1);
			var_rep(*p, *x) = ++v;
		}
	rule_sub(*p, r);
	return r;
}

rule rule_dup(lp *p, rule x, size_t o) {
	rule r = (rule){ .a = malloc(sizeof(term) * x.sz), .sz = o?x.sz-1:x.sz };
	size_t len = 0;
	rule_for_each_term(r, y, o) len += y->ar+1;
	int_t *t = malloc(sizeof(int_t) * len), *s = t;
	rule_for_each_term(r, y, o) term_for_each_sym(*y, z) *s++ = *z;
	for (size_t n = 0; n < r.sz; t += (r.a[n].ar=x.a[n].ar)+1) r.a[n++].a = t;
	rule_for_each_arg(x, y, o) if (*y > 0 && var_rep(*p, *y)) *y = var_rep(*p, *y);
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

bool rule_resolve(lp *p, size_t r, rule *n, rule *res) {
	if (*head(p->r[r]).a != *n->a->a || head(p->r[r]).ar != n->a->ar) return false;
	rule_reset_reps(*p, p->r[r]);
	rule_reset_reps(*p, *n);
	for (size_t i = 1; i <= head(p->r[r]).ar; ++i)
		if (!var_set_rep(*p, head(p->r[r]).a[i], *n->a->a, p->nv[r]))
			return false;
	*res = rule_dup(p, p->r[r], 0);
	return true;
}

bool edb_resolve(lp *p, term f, rule *n, rule *res) {
	if (*f.a != *n->a->a || f.ar !=n->a->ar) return false;
	rule_reset_reps(*p, *n);
	for (size_t i = 1; i <= f.ar; ++i)
		if (!var_set_rep(*p, f.a[i], n->a->a[i], 0))
			return false;
	*res = rule_dup(p, *n, 1);
	return true;
}

bool inst(state *s, lp *p, state *ss) {
	rule r;
	bool b = false;
	for (size_t n = 0; n < p->sz; ++n)
		for_each_active_rule(*s, x)
			if (rule_resolve(p, n, x, &r))
				b |= state_add_rule(ss, r, x);
	return b;
}

bool edb_reduce(lp *p, state *s, const db d, state *ss) {
	rule r;
	bool b = false;
	for_each_fact(d, x)
		for_each_inact_rule(*s, y)
			if (edb_resolve(p, *x, y, &r))
				b |= state_add_rule(ss, r, y);
	return b;
}

bool idb_reduce(lp *p, state *s, const db d, state *ss) {
	rule r;
	bool b = false;
	for_each_fact(d, x)
		for_each_inact_rule(*s, y)
			if (edb_resolve(p, *x, y, &r))
				b |= state_add_rule(ss, r, y);
	return b;
}

int main(int argc, char** argv) {
	sout = new(wchar_t);
	*sout = 0;

	setlocale(LC_CTYPE, "");
//	if (argc != 3 && argc != 4) er(usage);
	rule r;
	wchar_t *all;
	lp p = (lp){.r=0,.sz=0,.nv=0,.l=(labels){.a=0,.sz=0}};
	if (!(all = file_read_text(fopen(argv[1], "r")))) er(err_src);
	while (all && (r = rule_read(&p, &all)).a)
		lp_add_rule(p, r), rule_print(p, r, &sout, &outlen);
	fputws(sout, stdout);
}
