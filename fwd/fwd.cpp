#include "repl.h"

dict_t dict;
size_t unifications = 0;

void fwd::add2rule(term x, term y, clause h) {
	normvars(x, y, h);
	for (auto f : F) r22r1(x, y, h, f);
	R2.emplace(r2{{x, y}, h}), arity = max(arity, nvars({{x,y},h}));
}

void fwd::add(const term& t) { add_fact(t); }
#define pop(x) *x.erase(x.begin())

void fwd::addrule(clause b, const clause& h) {
loop:	if (b.empty()) return;
	if (b.size() == 1) { R1.emplace(*b.begin(), h); return; }
	const term &x = pop(b), &y = pop(b);
	if (b.size() > 2) {
		term i = interpolate(x, y, dict.tmp());
		b.emplace(i), add2rule(x, y, {i});
		goto loop;
	}
	add2rule(x, y, h);
}


void fwd::r22r1(const term& x, const term& y, const clause& h, const term& f) {
	tmpenv e = mkenv(arity);
	if (unify(x, f, e)) R1.emplace(sub(y, e), sub(h, e));
	if (envclear(e, arity), unify(y, f, e)) R1.emplace(sub(x, e), sub(h, e));
}

void fwd::r12r2(const term &b, const clause& h, const term &f) {
	if (tmpenv e = mkenv(arity); unify(b, f, e)) {
		clause hh = sub(h, e);
		for (const term& ff : hh)
			add_fact(ff);
	}
}

void fwd::add_fact(const term& f) {
	if (!F.emplace(f).second) return;
	tmpenv e = mkenv(arity);
	for (auto r : R2) {
		if (envclear(e, arity), unify(r.first.first, f, e)) {
			term b = sub(r.first.second, e);
			clause h = sub(r.second, e);
			if (R1.emplace(b, h).second)
				for (const term& ff : F) r12r2(b, h, ff);
		}
		if (envclear(e, arity), unify(r.first.second, f, e)) {
			term b = sub(r.first.first, e);
			clause h = sub(r.second, e);
			if (R1.emplace(b, h).second)
				for (const term& ff : F) r12r2(b, h, ff);
		}
	}
}
