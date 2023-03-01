#include "poset.h"
#include <numeric>
#include <map>

#ifndef NOOUTPUTS

#include "output.h"

#define OUT(x) x
#else
#define OUT(x)
#endif

using namespace std;

namespace { abs_cmp_ abs_cmp; }

static auto abs_lex_cmp = [](const std::pair<int_t, int_t> &p1,
		      const std::pair<int_t, int_t> &p2) {
    if (abs_cmp(p1.first, p2.first)) return true;
    if (p1.first == p2.first && abs_cmp(p1.second, p2.second)) return true;
    return false;
};

static auto abs_fst_cmp = [](auto &p1, auto &p2) {
    return abs_cmp(p1.first, p2.first);
};

// universe for positive and negative posets
vector<poset> P, NP;
unordered_map<poset, int_t> MP, MNP;

size_t std::hash<poset>::operator()(const poset &p) const {
	return hash_tri(p.eqs, p.imps, p.vars);
}

size_t std::hash<std::pair<int_t, std::pair<int_t, int_t>>>::operator()(
	const std::pair<int_t, std::pair<int_t, int_t>> &p) const {
	return hash_pair(p.first, hash_pair(p.second.first, p.second.second));
}

// Must be called after lift_vars due to initialization of eq_lift_hi/lo
void poset::lift_imps(poset &p, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo) {
	auto imp_lift = [](int_t fst, int_t snd, poset& p, poset& other, imap& lift) {
	    if (ps::contains(other.vars, -fst) ||
		pu::equal(other.eqs, fst, snd)) {
		    //TODO: Test if violation of antecedent should be lifted

		    // Implication is true in other since antecedent is violated
		    // or contained in equality
		    insert_imp(p, fst, snd);
	    } else if (ps::contains(other.vars, snd)) {
		    // Implication is trivially true in other or contained in equality
		    insert_imp(p, fst, snd);
		    if (ps::contains(other.vars, fst)) {
			    //In this case v -> h_imp.second is not allowed to be lifted later
			    lift.erase((abs_cmp(fst, snd) ? snd : fst));
		    }
	    } else p.pure = false;
	};

	auto h = pd::get_graph(hi.imps);
	auto l = pd::get_graph(lo.imps);

	auto h_iter = h.begin();
	auto l_iter = l.begin();

	while (h_iter != h.end() || l_iter != l.end()) {
		if(l_iter == l.end() || (h_iter != h.end() && abs_cmp(h_iter->first, l_iter->first))) {
			for(int_t h_suc = h_iter->second; h_suc != 0; h_suc = ps::next(h_suc)) {
				imp_lift(h_iter->first, ps::get(h_suc).e, p, lo, eq_lift_hi);
			}
			++h_iter;
		} else if (h_iter == h.end() || abs_cmp(l_iter->first, h_iter->first)) {
			for(int_t l_suc = l_iter->second; l_suc != 0; l_suc = ps::next(l_suc)) {
				imp_lift(l_iter->first, ps::get(l_suc).e, p, hi, eq_lift_lo);
			}
			++l_iter;
		} else {
			int_t h_suc = h_iter != h.end() ? h_iter->second : 0;
			int_t l_suc = l_iter != l.end() ? l_iter->second : 0;
			while (h_suc != 0 || l_suc != 0){
				if(l_suc == 0 || (h_suc != 0 && abs_cmp(h_suc, l_suc))) {
					imp_lift(h_iter->first, ps::get(h_suc).e, p, lo, eq_lift_hi);
					h_suc = ps::next(h_suc);
				} else if(h_suc == 0 || abs_cmp(l_suc, h_suc)) {
					imp_lift(l_iter->first, ps::get(l_suc).e, p, hi, eq_lift_lo);
					l_suc = ps::next(l_suc);
				} else {
					// Implication is contained in both lo and hi
					insert_imp(p, h_iter->first, ps::get(h_suc).e);
					h_suc = ps::next(h_suc);
					l_suc = ps::next(l_suc);
				}
			}
			++h_iter;
			++l_iter;
		}
	}
}

void poset::lift_vars(poset &p, int_t v, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo, pvector &eq_lift) {
	int_t h = hi.vars;
	int_t l = lo.vars;
	int_t h_var = ps::get(h).e;
	int_t l_var = ps::get(l).e;

	while (h != 0 || l != 0) {
		if (h == l) {
			// hi and lo have the same vars
			while (h != 0) {
				insert_var(p, h_var);
				h = ps::next(h);
				h_var = ps::get(h).e;
			}
			return;
		} else if (l == 0 || (h != 0 && abs(h_var) < abs(l_var))) {
			// Variable in hi but not in lo
			if (auto iter = eq_lift_lo.find(pu::find(lo.eqs, h_var));
				iter != eq_lift_lo.end()) {
				pu::merge(hi.eqs, iter->second, h_var);
			} else eq_lift_lo.emplace(pu::find(lo.eqs, h_var), h_var);
			h = ps::next(h);
			h_var = ps::get(h).e;
		} else if (h == 0 || abs(l_var) < abs(h_var)) {
			if (auto iter = eq_lift_hi.find(pu::find(hi.eqs, l_var));
				iter != eq_lift_hi.end()) {
				pu::merge(lo.eqs, iter->second, l_var);
			} else eq_lift_hi.emplace(pu::find(hi.eqs, l_var), l_var);
			// Here implications for the transitive closure have to be added.
			// But we want transitive reduction, therefore we don't add anything else.
			l = ps::next(l);
			l_var = ps::get(l).e;
		} else {
			// The absolute values of the variables are equal -> creates equality
			if (h_var == l_var) insert_var(p, h_var);
			else eq_lift.emplace_back(v,h_var);
			// Here implications for the transitive closure have to be added.
			// But we want transitive reduction, therefore we don't add anything else.
			h = ps::next(h);
			l = ps::next(l);
			h_var = ps::get(h).e;
			l_var = ps::get(l).e;
		}
	}
}

// Must be called after lift_vars due to initialization of eq_lift_hi/lo
void poset::lift_eqs(poset &p, int_t v, poset &hi, poset &lo,imap &eq_lift_hi, imap &eq_lift_lo, pvector& eq_lift) {
	int_t hi_eq = hi.eqs;
	int_t lo_eq = lo.eqs;
	
	// Lifting of implications due to variables
	for(auto &el : eq_lift_hi) {
		insert_imp(p, -v, el.second);
	}
	for(auto &el : eq_lift_lo) {
		insert_imp(p, v, el.second);
	}

	if (hi_eq == lo_eq) {
		// All equalities are lifted
		p.eqs = hi_eq;
	} else if (hi_eq != 0 && lo_eq != 0) {
		// Lifting of equalities contained in hi and lo
		p.eqs = pu::intersect(hi_eq, lo_eq);
		p.pure = false;
	} else if (hi_eq != 0 || lo_eq != 0) {
		p.pure = false;
	}
	for(auto& eq : eq_lift) {
		p.eqs = pu::merge(p.eqs, eq.first, eq.second);
	}
}

poset poset::lift(int_t v, int_t h, int_t l) {
	poset p;
	auto hi = get(h);
	auto lo = get(l);
	// Check if p can possibly be pure
	if (hi.pure && lo.pure) p.pure = true;
	imap eq_lift_hi, eq_lift_lo;
	pvector eq_lift;
	lift_vars(p, v, hi, lo, eq_lift_hi, eq_lift_lo, eq_lift);
	lift_imps(p, hi, lo, eq_lift_hi, eq_lift_lo);
	lift_eqs(p, v, hi, lo, eq_lift_hi, eq_lift_lo, eq_lift);
	p.v = abs(v); // v must be the smallest variable in p
	return p;
}

// Evaluate poset on the variable v
//TODO: Update variable v in p
poset poset::eval(const poset &p, int_t v) {
	//if (p.v != abs(v)) DBGFAIL;
	if (!p.pure) DBGFAIL;

	poset res = p;
	if (ps::contains(p.vars, v)) {
		res.vars = ps::remove(p.vars, v);
		return res;
	}

	if (ps::contains(p.vars, -v)) {
		return {};
	}

	vector<int_t> all_imp;
	for (auto el: pu::get_equal(res.eqs, v)) {
		if(ps::contains(res.vars, -el)) return {};
		res.vars = ps::insert(res.vars, el);
		res.imps = pd::set_var(res.imps, el, all_imp);
	}
	res.eqs = pu::rm_equal(res.eqs, v);
	for (int i = 0; i < (int) all_imp.size(); ++i) {
		for (auto el: pu::get_equal(res.eqs, all_imp[i])) {
			if(ps::contains(res.vars, -el)) return {};
			res.vars = ps::insert(res.vars, el);
			res.imps = pd::set_var(res.imps, el, all_imp);
		}
		res.eqs = pu::rm_equal(res.eqs, all_imp[i]);
	}
	res.vars = ps::remove(res.vars, v);
	return res;
}

bool poset::insert_var(poset &p, int_t v) {
	if (abs(v) < p.v || p.v == 0) p.v = abs(v);
	return (p.vars = ps::insert(p.vars, v));
}

poset poset::insert_var(poset &&p, int_t v) {
	p.vars = ps::insert(p.vars, v);
	if (abs(v) < p.v || p.v == 0) p.v = abs(v);
	return p;
}

void poset::insert_imp(poset &p, std::pair<int_t, int_t> &el) {
	if (abs(el.first) < p.v || p.v == 0) p.v = abs(el.first);
	if (abs(el.second) < p.v || p.v == 0) p.v = abs(el.second);
	// Extraction of created singletons and equalities
	vector<int_t> sings, eqs;
	p.imps = pd::insert(p.imps, el, sings, eqs);
	insert_eq(p, eqs);
	for(auto s : sings) p.vars = ps::insert(p.vars, s);
}

void poset::insert_imp(poset &p, int_t fst, int_t snd) {
	if (abs(fst) < p.v || p.v == 0) p.v = abs(fst);
	if (abs(snd) < p.v || p.v == 0) p.v = abs(snd);
	// Extraction of created singletons and equalities
	vector<int_t> sings, eqs;
	p.imps = pd::insert(p.imps, fst, snd, sings, eqs);
	insert_eq(p, eqs);
	for(auto s : sings) p.vars = ps::insert(p.vars, s);
}

void poset::insert_eq(poset &p, int_t v1, int_t v2) {
	if (abs(v1) < p.v || p.v == 0) p.v = abs(v1);
	if (abs(v2) < p.v || p.v == 0) p.v = abs(v2);
	p.eqs = pu::merge(p.eqs, v1, v2);
}

void poset::insert_eq(poset &p, vector<int_t> &eq) {
	if(eq.size() < 2) return;
	for(int_t i = 0; i < eq.size()-1; ++i)
		p.eqs = pu::merge(p.eqs, eq[i], eq[i+1]);
}

poset poset::get(int_t pos) {
	return (pos > 0 ? P[pos] : NP[-pos]);
}

bool poset::operator==(const poset &p) const {
	return p.vars == vars && p.imps == imps &&
	       p.eqs == eqs && p.pure == pure;
}

void poset::print(poset &p, ostream &os) {
	pu::print(p.eqs, os);
	pd::print(p.imps, os);
	os << endl;
	ps::print(p.vars, os);
}

void poset::print(poset &&p, ostream &os) {
	print(p, os);
}

// Assumes that poset can be negated purely
poset poset::negate(const poset &p) {
	int_t imp_size = pd::size(p.imps);
	int_t var_size = ps::size(p.vars);
	if (auto eq = pu::elems(p.eqs); eq.size() == 1) {
		int_t fst = eq[0], snd = pu::find(p.eqs, fst);
		poset np;
		return poset::insert_eq(np, fst, -snd), np;
	} else if (imp_size <= 2 && var_size == 0) {
		auto g = pd::get_graph(p.imps);
		auto it = g.begin();
		if(imp_size == 1) {
			poset np;
			poset::insert_var(np, it->first);
			poset::insert_var(np, -ps::get(it->second).e);
			return np;
		} else {
			int_t a = it->first;
			int_t b = ps::get(it->second).e;
			++it;
			int_t c = it->first;
			int_t d = ps::get(ps::next(it->second)).e;
			poset np;
			poset::insert_imp(np, -a, c);
			poset::insert_imp(np, b, c);
			poset::insert_imp(np, -a, -d);
			poset::insert_imp(np, b, -d);
			return np;
		}
	} else if (imp_size == 4 && var_size == 0) {
		auto g = pd::get_graph(p.imps);
		auto it = g.begin();
		int_t a = -it->first, c = ps::get(it->second).e;
		++it;
		int_t b = it->first, d = -ps::get(ps::next(it->second)).e;
		poset np;
		return poset::insert_imp(np, a, b), poset::insert_imp(np, c, d), np;
	} else if (var_size <= 2 && imp_size == 0) {
		if(var_size == 1) {
			poset np;
			return poset::insert_var(np, -ps::get(p.vars).e), np;
		} else {
			int_t fst = ps::get(p.vars).e;
			int_t snd = ps::get(ps::get(p.vars).n).e;
			poset np;
			return poset::insert_imp(np, fst, -snd), np;
		}
	} else {
		DBG(assert(var_size == 1 && imp_size == 1));
		auto g = pd::get_graph(p.imps);
		auto it = g.begin();
		int_t a = it->first;
		int_t b = ps::get(it->second).e;
		int_t c = ps::get(p.vars).e;
		poset np;
		poset::insert_imp(np, -a, -c);
		poset::insert_imp(np, b, -c);
		return np;
	}
}

bool poset::negatable(poset &p) {
	if (p.eqs == 0) {
		if (ps::size(p.vars) + pd::size(p.imps) <= 2)
			return true;
		else {
			auto g = pd::get_graph(p.imps);
			if(g.size() != 2) return false;
			auto it = g.begin();
			int_t c = ps::get(it->second).e;
			int_t d = ps::get(ps::next(it->second)).e;
			++it;
			return c == ps::get(it->second).e && d == ps::get(ps::next(it->second)).e;
		}
	} else return pu::elems(p.eqs).size() < 2 && p.vars + p.imps == 0;
}
