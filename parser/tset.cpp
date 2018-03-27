#include "tset.h"

vec buf = (vec)memset(new int_t[max_arity], 0, sizeof(int_t) * max_arity);

int icmp(vecc x, vecc y, size_t len) {
	for (size_t n=0;n<len;++n) if (x[n]!=y[n]) return x[n]<y[n] ? -1 : 1;
	return 0;
}

bool tset::cmp::operator()(vecc x, vecc y) const {
	return x[k] != y[k] ? x[k] < y[k] : ::icmp(x, y, a) < 0;
}

tset::set_iter tset::first(size_t n, int_t i) const {
	auto it = s[n]->lower_bound((buf[n] = i, buf));
	return buf[n] = 0, it;
}

tset::tset(size_t arity): arity(arity), s(new set<vecc,cmp>*[arity]) {
	for(size_t n = 0; n < arity; ++n) s[n]=new set<vecc,cmp>(cmp(n,arity));
}
void tset::add(vecc t) { for(size_t n = 0; n < arity; ++n) s[n]->emplace(t); }

vecc tset::first(vecc pat, iters& it) const {
	for (size_t n = 0; n < arity; ++n)
		if (pat[n] < 0) continue;
		else if (auto lb = first(n, pat[n]); lb != s[n]->end())
			it.push_back({n, {lb, first(n, pat[n] + 1)}});
		else return 0;
	return next(pat, it);
}

bool rep(env& e, int_t v, int_t c) {
	if (auto it = e.find(v); it == e.end())
		return e.emplace(v, c), true;
	else return it->second == c;
}

#define has(it, x, y) ((it = (x).lower_bound(y)) != (x).end())
vecc tset::next(vecc pat, iters& it) const {
	int c;
	vecc r;
loop:	bool b = false;
	env e;
	if (it[0].second[0] == it[0].second[1]) return 0;
	for (size_t n = 1; n < it.size(); ++n)
		if (auto &jt = it[n].second[0], &kt = it[n-1].second[0];
			jt == it[n].second[1] ||
			((c = ::icmp(*jt, *kt, arity)) < 0 && (b = true) &&
				!has(jt, *s[it[n].first], *kt)) ||
			(c > 0 && (b = true) && !has(kt,*s[it[n-1].first],*jt)))
			return 0;
	if (b) goto loop;
	r = *(it[0].second[0]++);
	for (size_t n = 0; n < arity; ++n)
		if (pat[n] < 0 && !rep(e, pat[n], r[n]))
			goto loop;
	return r;
}

int main(int, char**) {
	tset s(3);
	int_t a[]={1,2,3}, b[]={1,2,2}, c[]={1,2,4}, d[]={1,1,3}, e[]={4,3,4},
		q[]={1,-4,-4};
	vecc r;
	s.add(a), s.add(b), s.add(c), s.add(d), s.add(e);
	tset::iters it;
	assert(r = s.first(q, it));
	for (size_t n = 0; n < 3; ++n) cout << r[n] << ' ';
	cout << endl;
	while ((r = s.next(q, it))) {
		for (size_t n = 0; n < 3; ++n) cout << r[n] << ' ';
		cout << endl;
	}
}
