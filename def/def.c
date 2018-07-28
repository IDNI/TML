#include "def.h"
#include <unistd.h>

dict_t *dict = 0;
stack_t *stack = 0;
wchar_t **gconsts = 0, **gvars = 0;
int_t *vardata = 0;
constdata *cdata = 0;
size_t gnconsts = 0, gnvars = 0;

uint32_t hash(const wchar_t* s, size_t n) {
	uint32_t h = 1;
	while (n--) h *= 1 + *s * __builtin_bswap32(*s), ++s;
	return h;
}

int_t _str_to_id(dict_t **d, const wchar_t* s, size_t n) {
	uint32_t h = hash(s, n);
	if (!*d) {
		if (*s == L'?')
			return	array_append(gvars, const wchar_t*, gnvars, s),
				resize(vardata, void*, gnvars), vardata[gnvars-1] = 0,
				(*(*d = new(dict_t)) = (dict_t){ .s=s, .h=h, .id = gnvars, .l=0, .r=0, .n=n }).id;
		else return array_append(gconsts, const wchar_t*, gnconsts, s),
			resize(cdata, constdata, gnconsts),
			memset(&cdata[gnconsts-1], 0, sizeof(constdata)),
			(*(*d = new(dict_t)) = (dict_t){ .s=s, .h=h, .id = -gnconsts, .l=0, .r=0, .n=n }).id;
	}
	return	(h == (**d).h && n == (**d).n && !wmemcmp((**d).s, s, n))
		? (**d).id
		: _str_to_id((**d).h < h ? &(**d).l : &(**d).r, s, n);
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

alt* alt_create(int_t r, size_t ar) {
	alt *a = new(alt);
	*a = (alt){ .eq = 0, .terms = 0, .nvars = ar, .nterms = 0, .hsz = ar, .r = r };
	if (ar) a->eq=calloc(ar, sizeof(int_t));
	return a;
}

void alt_delete(alt* a) { if (!a) return; if (a->eq) free(a->eq); if (a->terms) free(a->terms); }

void alt_add_term(alt* a, term t) {
	if (t.ar) memset(resize(a->eq, int_t, a->nvars+t.ar)+a->nvars,0,sizeof(int_t)*t.ar);
	array_append(a->terms, term, a->nterms, t), a->nvars += t.ar;
}

int_t alt_get_rep(alt *a, int_t v) {
	if (v > 0) assert((size_t)v <= a->nvars);
	else assert((size_t)-v <= gnconsts);
	if (!a->eq || v < 0 || !a->eq[v-1]) return v;
	if (v == a->eq[v-1]) return a->eq[v-1] = 0, v;
	return a->eq[v-1] = alt_get_rep(a, a->eq[v-1]);
}

bool alt_add_eq(alt *a, int_t x, int_t y) {
	x = alt_get_rep(a, x), y = alt_get_rep(a, y);
	bool r = x==y?true:x<0?y<0?false:((a->eq[y-1]=x),true):((x>y?(a->eq[x-1]=y):(a->eq[y-1]=x)),true);
	return r;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

alt* alt_add_raw(int_t *h, int_t **b, size_t nh, size_t nb, size_t *sz) {
	size_t i, j;//, r;
	int_t d, v;
	alt *a = alt_create(*h, nh);
	for (i = 0, v = nh; i < nb; ++i) {
		alt_create_term(a, *b[i], sz[i], v), v += sz[i];
		for (j = 1; j <= sz[i]; ++j)
			if (b[i][j] > 0) {
				if (gnvars <= (size_t)b[i][j]) alloc_vardata(b[i][j]+1);
				id_set_vardata(b[i][j], 0);
			}
	}
	for (i = 1; i <= nh; ++i)
		if (h[i] > 0) {
			if (gnvars <= (size_t)h[i]) alloc_vardata(h[i]+1);
			id_set_vardata(h[i], 0);
		}
	for (i = 1; i <= nh; ++i)
		if (h[i] < 0) alt_add_eq(a, i, h[i]);
		else if ((d = (int_t)id_get_vardata(h[i]))) alt_add_eq(a, i, d);
		else id_set_vardata(h[i], i);
	for (i = 0, v = nh+1; i < nb; ++i)
		for (j = 1; j <= sz[i]; ++j, ++v)
			if (b[i][j] < 0) alt_add_eq(a, v, b[i][j]);
			else if ((d = (int_t)id_get_vardata(b[i][j]))) alt_add_eq(a, v, d);
			else id_set_vardata(b[i][j], v);
	return a;
//	r = def_add_alt(def_get(*h, nh, src), a);
//	return def_get(*h, nh, src)->a[r];
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

def* def_create(int_t h, size_t ar, bool src) {
	def *d = new(def);
	if (src) id_get_cdata(h).src = d;
	else id_get_cdata(h).dst = d;
	return *d = (def){ .h = term_create(h, ar, 0), .a = 0, .sz = 0 }, d;
}

def* def_get(int_t h, size_t ar, bool src) {
	def *d = src ? id_get_cdata(h).src : id_get_cdata(h).dst;
	return d ? d : def_create(h, ar, src);
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////

wchar_t* str_read(int_t *r, wchar_t *in) {
	wchar_t *s = in;
	while (*s && iswspace(*s)) ++s;
	if (!*s) return 0;
	wchar_t *t = s;
	if (*t == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == s) return 0;
	*r = str_to_id(s, t - s);
	while (iswspace(*t)) ++t;
	return t;
}

int_t* term_read(size_t *sz, wchar_t **in) {
	int_t x, *t = 0;
	*sz = 0;
	while ((*in = str_read(&x, *in))) {
		array_append(t, int_t, *sz, x);
		if (!iswalnum(**in) && **in != L'?') return --*sz, t;
	}
	return 0;
}

void id_print(int_t n) {
	if (n > 0) {
		wprintf(L"?%d", n);
		return;
	}
	const wchar_t *s = str_from_id(n);
	while (iswalnum(*s)) putwchar(*s++);
}

void term_print(const term t, size_t v) {
	id_print(t.r);
	for (size_t n = 1; n <= t.ar; ++n) wprintf(L" ?%zu", n + v);
}

alt* alt_read(wchar_t **in) {
	if (!*in) return 0;
	int_t **b = 0, *h = 0, *t;
	size_t nb = 0, nsz = 0, *sz = 0, nh = 0, s;
	if (!(h = term_read(&nh, in))) return 0;
//	if (src) array_append(srcs, int_t, nsrcs, *h); else array_append(dsts, int_t, ndsts, *h);
	if (**in == L'.') return ++*in, alt_add_raw(h, 0, nh, 0, 0);
	else if (*((*in)++) != L':') perror("':' expected\n"), exit(1);
	while ((t = term_read(&s, in))) {
		if (	array_append(b, int_t*, nb, t),
			array_append(sz, size_t, nsz, s),
			**in != L',') {
				if (*((*in)++) != L'.') perror("'.' expected\n"), exit(1);
				return alt_add_raw(h, b, nh, nb, sz);
			}
		else ++*in;
	}
	return 0;
}

void alt_print(alt* a) {
	term_print(term_create(a->r, a->hsz, 0), 0);
	size_t v = a->hsz;
	for (size_t n = 0; n < a->nterms; ++n)
		wprintf(L", "), term_print(a->terms[n], v), v += a->terms[n].ar;
	wprintf(L". [");
	int_t k;
	for (size_t n = 1; n <= a->nvars; ++n)
		if ((k = alt_get_rep(a, n)) > 0) { if ((size_t)k != n) wprintf(L" ?%zu = ?%lu; ", n, k); }
		else if (k < 0) wprintf(L" ?%zu = %s; ", n, str_from_id(k));
	wprintf(L"]\n");
}

int alt_cmp(const alt *x, const alt *y) {
	if (x == y) return 0;
	if (!x) return 1;
	if (!y) return -1;
	if (x->nterms != y->nterms) return x->nterms > y->nterms ? 1 : -1;
	if (x->nvars != y->nvars) return x->nvars > y->nvars ? 1 : -1;
	int r = memcmp(x->terms, y->terms, sizeof(term) * x->nterms);
	if (r) return r;
	assert(x->hsz == y->hsz);
	size_t n;
	for (n = 1; n <= x->hsz; ++n)
		if (alt_get_rep((alt*)x, n) > 0) break;
		else if (alt_get_rep((alt*)y, n) > 0) break;
		else if (alt_get_rep((alt*)x, n) != alt_get_rep((alt*)y, n)) break;
	if (n == x->hsz+1) return 0;
	if (x->eq && y->eq) return memcmp(x->eq, y->eq, sizeof(int_t) * (x->nvars+1));
	return x->eq > y->eq ? 1 : -1;
}

size_t def_add_alt(def *d, alt *a) {
	for (size_t n = 0; n < d->sz; ++n) if (!alt_cmp(d->a[n], a)) return n;
	return array_append(d->a, alt*, d->sz, a), d->sz-1;
}

void def_print(int_t t, bool src) {
	def *d = src ? id_get_cdata(t).src : id_get_cdata(t).dst;
	if (!d) return;
	for (size_t n = 0; n < d->sz; ++n)
		term_print(d->h, 0), wprintf(L": "), alt_print(d->a[n]), wprintf(L".\n");
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
		else if (c == L'\n') skip = false, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0;
		all = wcscat(resize(all, wchar_t, wcslen(all) + 32), buf);
		goto next;
	} else if (skip) goto next;
	return all;
}

void alt_deflate(alt *a, int_t **h, int_t ***b, size_t **sz, size_t *nb, size_t *nh) {
	if (!a) return;
	*h = arr(int_t, a->hsz+1), **h = a->r,
	*b = arr(int_t*, a->nterms), *sz = arr(size_t, a->nterms);
	*nb = a->nterms, *nh = a->hsz;
	size_t v = 0;
	for (size_t n = 0; n < a->hsz; ++n)
		(*h)[n+1] = alt_get_rep(a, ++v);
	for (size_t n = 0, m = 0; n < a->nterms; ++n, ++m) {
		(*b)[m] = arr(int_t, a->terms[n].ar + 1);
		*((*b)[m]) = a->terms[n].r;
		(*sz)[m] = a->terms[n].ar+1;
		for (size_t k = 0; k < a->terms[n].ar; ++k)
			(*b)[n][k+1] = alt_get_rep(a, ++v);
		for (size_t k = 0; k < n; ++k)
			if ((*sz)[n] == (*sz)[k] && !memcmp((*b)[n], (*b)[k], (*sz)[n] * sizeof(int_t))) {
				free((*b)[m--]);
				break;
			}
	}
}

void alt_deflate_print(alt *a) {
	if (!a) return;
	int_t *h = 0, **b = 0;
	size_t *sz = 0, nb, nh;
	alt_deflate(a, &h, &b, &sz, &nb, &nh);
	for (size_t n = 0; n <= nh; ++n) id_print(h[n]), putwchar(L' ');
	if (nb) putwchar(L':');
	for (size_t n = 0; n < nb; ++n) {
		for (size_t k = 0; k < sz[n]; ++k)
			id_print(b[n][k]), putwchar(L' ');
		if (n+1!=nb) putwchar(L',');
	}
	wprintf(L".\n");
}

void def_deflate_print(def *d) {
	for (size_t n = 0; n < d->sz; ++n) alt_deflate_print(d->a[n]);
}

const char usage[] = "Usage: <src filename> <dst filename>\nWill output the program after plugging src into dst.\n)";

int main(int argc, char** argv) {
	int_t y, l, m;
	size_t n, k, t, nd, ns, nsrc = 0, ndst = 0;
	//def *ds, *dd;
	alt *r, **src = 0, **dst = 0;
	wchar_t *all;

	setlocale(LC_CTYPE, "");
	if (argc != 3) perror(usage), exit(1);
	for (all = file_read_text(fopen(argv[1], "r")); all;) if ((r = alt_read(&all))) array_append(src, alt*, nsrc, r);
	for (all = file_read_text(fopen(argv[2], "r")); all;) if ((r = alt_read(&all))) array_append(dst, alt*, ndst, r);

	t = k = n = nd = ns = 0;
	for (nd = 0; nd < ndst; ++nd)
	for (t = 0; t < dst[nd]->nterms; ++t)
	for (ns = 0; ns < nsrc; ++ns) {
	if (dst[nd]->terms[t].r != src[ns]->r || dst[nd]->terms[t].ar != src[ns]->hsz) continue;
	alt		*da = dst[nd], *sa = src[ns];//dd->a[j], *sa = ds->a[n];
	const int_t	dnterms = da->nterms, snterms = sa->nterms,
			dnvars = da->nvars, snvars = sa->nvars,
			v0 = da->terms[t].v0, ar = da->terms[t].ar, v1 = v0 + ar - 1;
	int_t *ssub = stack_arr(int_t, ar), *dsub = stack_arr(int_t, ar);
	alt_deflate_print(sa);
	alt_print(sa);
	alt_deflate_print(da);
	alt_print(da);
	r = alt_create(da->r, da->hsz);

	for (l = 0;	l <  dnterms;++l) if (l != (int_t)t) alt_add_term(r, da->terms[l]);
	for (l = 0;	l <  snterms;++l) alt_add_term(r, sa->terms[l]);

	for (l = v0;	l <= v1 ; ++l)
		if ((y = alt_get_rep(da, l+1)) < 0)
			dsub[l-v0] = y;

	for (l = 0;	l <  ar ; ++l)
		if ((y = alt_get_rep(sa, l+1)) < 0 || (y > v0 && y <= v1))
			ssub[l] = y;

	for (;		l < snvars; ++l)
		if ((y = alt_get_rep(sa, l+1)) > 0 && y <= ar )
			if (ssub[y-1]>=0) ssub[y-1] = l;

	for (l = 1;	l <= v0;     ++l)
		if ((y = alt_get_rep(da, l)) > v0 && y <= v1+1)
			if (dsub[y-v0-1]>=0) dsub[y-v0-1] = l;

	for (;		l < v1+1;    ++l)
		if ((y = alt_get_rep(da, l)) <= v0 || y > v1+1)
			dsub[l-v0-1] = y;

	for (;		l <= dnvars; ++l)
		if ((y=alt_get_rep(da,l)) > v0 && y <= v1+1)
			if (dsub[y-v0-1]>=0) dsub[y-v0-1] = l;

	for (l = 0;	l < ar; ++l) wprintf(L"ssub %d %d\n", l, ssub[l]);
	for (l = 0;	l < ar; ++l) wprintf(L"dsub %d %d\n", l, dsub[l]);

	for (l = m = 0;	l <  v0;     ++l)
		r->eq[m++] = 	da->eq[l] > v0 && da->eq[l] <= v1+1
				? ssub[da->eq[l-v0]] ? ssub[da->eq[l-v0]]
				: da->eq[l] : da->eq[l];

	for (l = v1+1;	l <  dnvars; ++l)
		r->eq[m++] =	da->eq[l] > v0 && da->eq[l] <= v1+1
				? ssub[da->eq[l-v0]] ? ssub[da->eq[l-v0]]
				: da->eq[l] : da->eq[l];

	for (l = ar+1;	l <  snvars; ++l)
		r->eq[m++] =	sa->eq[l] <= ar && sa->eq[l] > 0
				? dsub[sa->eq[l]-1] ? dsub[sa->eq[l]-1]
				: sa->eq[l] < 0 ? sa->eq[l] :
				(sa->eq[l]+dnvars-2*ar) : (sa->eq[l]+dnvars-2*ar);

	for (l = v0+1;	l <= v1;     ++l)
		if (!(y = alt_get_rep(da, l))) continue;
		else for (m = l + 1; m <= v1; ++m)
			if (y == alt_get_rep(da, m))
				alt_add_eq(r, dsub[l-v0-1], dsub[m-v0-1]);

	for (l = 0;	l <  ar;     ++l)
		if (!(y = alt_get_rep(sa, l+1))) continue;
		else for (m = l + 1; m < ar; ++m)
			if (y == alt_get_rep(sa, m+1))
				if (ssub[l] && ssub[m]) alt_add_eq(r, ssub[l], ssub[m]);

	for (l = 0;	l < ar; ++l) if (ssub[l] && dsub[l]) alt_add_eq(r, ssub[l], dsub[l]);

	alt_deflate_print(r);
	alt_print(r);
	}
}
