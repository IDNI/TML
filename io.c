#include "ed.h"

wchar_t *sout = 0;
size_t outlen = 0;

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

dict* dict_get_str(labels l, int_t n) { return n > 0 ? &l.a[n-1] : &l.a[-n-1]; }

wchar_t* str_read(lp p, int_t *r, wchar_t *in) {
	wchar_t *s = in, *t;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	if (*(t = s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	while (iswspace(*t)) ++t;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = dict_get(&p.l, s, t - s);
	while (*t && iswspace(*t)) ++t;
	return t;
}

term term_read(lp p, wchar_t **in) {
	int_t x;
	term r = (term){ .a = 0, .ar = 0 };
	while (**in != L')' && (*in = str_read(p, &x, *in))) {
		if (!r.ar && *((*in)++) != L'(') er(oparen_expected);
		array_append(r.a, int_t, r.ar, x);
		if (**in == L',') ++*in;
		else if (**in == L')') break;
		else if (r.ar != 1) er(comma_expected);
	}
	for (++*in; iswspace(**in); ++*in);
	return --r.ar, r;
}

wchar_t tmp[128];
void id_print(lp p, int_t n, wchar_t **out, size_t *len) {
	if (n > 0) out_str_f(L"?%d", n);
	else {
		ws s = dict_get_str(p.l, n)->s;
		size_t l = dict_get_str(p.l, n)->n;
		if (l >= 8 && !wcsncmp(s,L"default:", 8)) (s += 8), l -= 8;
		wcsncat(*out = str_resize(*out, *len, l), s, l);
	}
}

void term_print(lp p, const term t, wchar_t **out, size_t *len) {
	id_print(p, *t.a > 0 ? -*t.a : *t.a, out, len);
	wcscat(str_resize(*out, *len, 1), L"(");
	term_for_each_arg(t, x) {
		id_print(p, *x, out, len);
		if (x != &t.a[t.ar])// putwchar(L',');
			wcscat(str_resize(*out, *len, 1), L",");
	}
	wcscat(str_resize(*out, *len, 1), L")");
}

void rule_add_term(rule *c, const term t) {
//	term_for_each_arg(t, x) if (*x > 0) ++c->nvars, *x = var_get_rep(*x);
	rule_for_each_term(*c, x, 1)
		if (sameterm(*x, t))
			return;
	array_append(c->a, term, c->sz, t);
}

rule rule_read(lp p, wchar_t **in) {
	rule c = (rule){.a=0,.sz=0};
	while (iswspace(**in)) ++*in;
	if (!**in) return c;
	term t = term_read(p, in);
	if (!t.a) return c;
	term_for_each_arg(t, x) if (*x > 0) var_rep(p, *x) = 0;
	rule_add_term(&c, t);
	if (**in == L'.') return ++*in, c;
	if (*((*in)++) != L':' || *((*in)++) != L'-') er(entail_expected);
next:	if (!(t = term_read(p, in)).a) return c;
	term_for_each_arg(t, x) if (*x > 0) var_rep(p, *x) = 0;
	rule_add_term(&c, t);
	if (**in != L'.') goto next;
	rule_normvars(p, c);
	return ++*in,  c;
}

wchar_t* file_read_text(FILE *f) {
	wchar_t *all = new(wchar_t), buf[32];
	wint_t c;
	*buf = *all = 0;
	size_t n, l;
	bool skip = false;
next:	for (n = l = 0; n < 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = false; break; }
		else if (c == L'#') skip = true;
		else if (c == L'\r' || c == L'\n') skip = false, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0;
		all = wcscat(resize(all, wchar_t, wcslen(all) + 32), buf);
		goto next;
	} else if (skip) goto next;
	return all;
}

void rule_print(lp p, const rule a, wchar_t **out, size_t *len) {
	term_print(p, *a.a, out, len);
	if (a.sz > 1) wcscat(str_resize(*out, *len, 4), L" :- ");
	for (size_t n = 1; n < a.sz; ++n)
		term_print(p, a.a[n], out, len),
		wcscat(str_resize(*out, *len, 1), n == a.sz - 1 ? L" ." : L", ");
}
