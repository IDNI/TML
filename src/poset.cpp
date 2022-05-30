#include "poset.h"

#ifndef NOOUTPUTS

#include "output.h"

#define OUT(x) x
#else
#define OUT(x)
#endif

using namespace std;

auto abs_cmp = [](int_t a, int_t b) {
    int_t abs_a = abs(a), abs_b = abs(b);
    if (abs_a < abs_b) return true;
    if (abs_b < abs_a) return false;
    return a < b;
};

auto abs_lex_cmp = [](const std::pair<int_t, int_t> &p1,
		      const std::pair<int_t, int_t> &p2) {
    if (abs_cmp(p1.first, p2.first)) return true;
    if (p1.first == p2.first && abs_cmp(p1.second, p2.second)) return true;
    return false;
};

// universe for positively saved posets
vector<poset> P;
// universe for negatively saved posets
vector<poset> NP;

std::vector<PersistentUnionFind> uf_univ;
std::vector<PersistentPairs> pairs_univ;
std::vector<PersistentSet> set_univ;
std::unordered_map<PersistentUnionFind, int_t> memo;
std::unordered_map<PersistentPairs, int_t> pair_memo;
std::unordered_map<PersistentSet, int_t> set_memo;
unordered_map<pair<int_t, int_t>, int_t> set_cache;
unordered_map<pair<int_t, pair<int_t, int_t>>, int_t> pair_cache;

size_t std::hash<PersistentUnionFind>::operator()(
	const PersistentUnionFind &uf) const {
	return uf.hash;
}

size_t std::hash<PersistentSet>::operator()(const PersistentSet &s) const {
	return hash_pair(s.e, s.n);
}

size_t std::hash<PersistentPairs>::operator()(const PersistentPairs &p) const {
	std::hash<std::pair<int_t, int_t>> hasher;
	return hash_pair(hasher(p.e), p.n);
}

size_t std::hash<poset>::operator()(const poset &p) const {
	return hash_tri(p.eqs, p.imps, p.vars);
}

size_t std::hash<std::pair<int_t, int_t>>::operator()(
	const std::pair<int_t, int_t> &p) const {
	return hash_pair(p.first, p.second);
}

size_t std::hash<std::pair<int_t, std::pair<int_t, int_t>>>::operator()(
	const std::pair<int_t, std::pair<int_t, int_t>> &p) const {
	return hash_pair(p.first, hash_pair(p.second.first, p.second.second));
}


int_t PersistentArray::get(storage &arr, const sppa &t, int_t pos) {
	if (t->diff == nullptr) {
		// Here we operate directly on the vector
		return arr[pos];
	}
	reroot(arr, t);
	DBG(assert(t->diff == nullptr));
	return arr[pos];
}

PersistentArray::sppa
PersistentArray::set(storage &arr, const sppa &t, int_t pos, int_t val) {
	reroot(arr, t);
	// The hash also stays the same in this situation
	if (get(arr, t, pos) == val) return t;

	DBG(assert(t->diff == nullptr));
	int_t old_val = arr[pos];
	arr[pos] = val;
	auto res = make_shared<PersistentArray>(PersistentArray());
	t->p = pos;
	t->v = old_val;
	t->diff = res;
	return res;
}

// This function must only be called directly after a set command and not at a later point in time
void
PersistentArray::undo(storage &arr, const sppa &current, const sppa &last) {
	DBG(assert(current->diff == nullptr));

	arr[last->p] = last->v;
	last->diff = nullptr;
}

void PersistentArray::reroot(storage &arr, const sppa &t) {
	if (t->diff == nullptr) return;
	reroot(arr, t->diff);
	DBG(assert(t->diff->diff == nullptr));
	int_t pos = t->p;
	int_t val = arr[pos];
	arr[pos] = t->v;
	shared_ptr<p_arr> arr_pt = t->diff;

	t->p = t->diff->p;
	t->v = t->diff->v;
	t->diff = t->diff->diff;

	arr_pt->diff = t;
	arr_pt->p = pos;
	arr_pt->v = val;
}

vector<int_t> PersistentUnionFind::parent_s;
vector<int_t> PersistentUnionFind::link_s;
vector<int_t> PersistentUnionFind::hashes_s;

void PersistentUnionFind::init(int_t n) {
	if (!uf_univ.empty()) return;
	puf root = puf(n);
	uf_univ.push_back(root);
	memo.try_emplace(move(root), 0);
}

int_t PersistentUnionFind::find(const puf &t, int_t elem) {
	auto t_elem = p_arr::get(parent_s, t.arr_pt, abs(elem));
	if (abs(t_elem) == abs(elem)) return elem < 0 ? -t_elem : t_elem;
	else {
		auto r = elem < 0 ? -find(t, t_elem) : find(t, t_elem);
		t.arr_pt = p_arr::set(parent_s, t.arr_pt, abs(elem),
				      elem < 0 ? -r : r);
		// We do not reset the hashes because those are only queried on root nodes
		return r;
	}
}

int_t PersistentUnionFind::find(int_t t, int_t elem) {
	auto &uf = uf_univ[t];
	return find(uf, elem);
}

// Updates t by setting the value at x to y
// while assuming that x and y are root nodes
// y is the new parent of x
int_t PersistentUnionFind::update(const puf &t, int_t x, int_t y) {
	DBG(assert(y >= 0));
	auto hash_x = p_arr::get(hashes_s, t.hash_pt, abs(x));
	auto hash_y = p_arr::get(hashes_s, t.hash_pt, y);
	auto uf = puf(p_arr::set(parent_s, t.arr_pt, abs(x), x < 0 ? -y : y),
		      update_link(t, x, y),
		      p_arr::set(hashes_s, t.hash_pt, y,
				 hash_set(x, y, hash_x, hash_y)),
		      t.hash, x, y, hash_x, hash_y);
	return add(uf);
}

int_t PersistentUnionFind::add(puf &uf) {
	if (auto it = memo.find(uf); it != memo.end()) {
		return it->second;
	} else {
		uf_univ.push_back(uf);
		memo.try_emplace(move(uf), uf_univ.size() - 1);
		return (int_t) uf_univ.size() - 1;
	}
}

PersistentUnionFind::sppa
PersistentUnionFind::update_link(const puf &t, int_t x, int_t y) {
	// y is the new parent of x
	DBG(assert(y >= 0));
	int_t y_link = p_arr::get(link_s, t.link_pt, y);
	int_t x_link = p_arr::get(link_s, t.link_pt, abs(x));

	auto link1 = p_arr::set(link_s, t.link_pt, y, x < 0 ? -x_link : x_link);
	return p_arr::set(link_s, link1, abs(x), x < 0 ? -y_link : y_link);
}

int_t PersistentUnionFind::merge(int_t t, int_t x, int_t y) {
	auto form = [](int_t &x, int_t &y) {
	    //y will hold the lower variable number
	    if (abs(x) < abs(y)) swap(x, y);
	    //y will be positive
	    if (y < 0) x = -x, y = -y;
	};
	form(x, y);
	auto &uf = uf_univ[t];
	auto cx = puf::find(uf, x);
	auto cy = puf::find(uf, y);
	form(cx, cy);
	if (cx != cy) {
		if (abs(cy) < abs(cx)) return update(uf, cx, cy);
		else
			assert(false);
		return 0;
	} else return t;
}

int_t PersistentUnionFind::intersect(int_t t1, int_t t2) {
	if (t1 == t2) return t1;
	else if (t1 == 0 || t2 == 0) return 0;

	static map<pair<int_t, int_t>, vector<int_t>> eq_classes;
	eq_classes.clear();

	auto &uf1 = uf_univ[t1];
	auto &uf2 = uf_univ[t2];

	// Make uf1 root, so we check the diff path from uf2
	p_arr::reroot(parent_s, uf1.arr_pt);
	weak_ptr<p_arr> diff_pt = uf2.arr_pt;

	vector<pair<int_t, int_t>> diffs;
	while (diff_pt.lock()->diff != nullptr) {
		auto el = make_pair(diff_pt.lock()->p, 0);
		if (!binary_search(diffs.begin(), diffs.end(), el)) {
			diffs.emplace_back(move(el));
			sort(diffs.begin(), diffs.end());
		}
		diff_pt = diff_pt.lock()->diff;
	}

	for (auto &el: diffs) {
		el.second = find(uf1, el.first);
	}

	int_t result = t2;
	for (auto &el: diffs) {
		// Now create equivalence pairs
		int_t eq_class_uf2 = find(uf2, el.first);
		if (el.first == el.second || el.first == eq_class_uf2) {
			// Element is set representative --> no further equality possible in intersection
			t2 = remove(t2, el.first);
		}
		if (el.second < 0) {
			eq_classes[{-el.first, -eq_class_uf2}].emplace_back(
				-el.first);
		} else {
			eq_classes[{el.first, eq_class_uf2}].emplace_back(
				el.first);
		}
	}

	for (const auto &p: eq_classes) {
		// Remove singletons
		if (p.second.size() == 1) t2 = remove(t2, p.second[0]);
		// Merge equivalence classes --> already done?!
		//else if (p.second.size() > 1) {
		//  for(const auto& el : p.second)
		//    merge(t2,p.second[0],el);
		//}
	}
	return result;
}

bool PersistentUnionFind::equal(int_t t, int_t x, int_t y) {
	auto &uf = uf_univ[t];
	return find(uf, x) == find(uf, y);
}

bool PersistentUnionFind::operator==(const puf &uf) const {
	//Quickcheck hashes
	if (hash != uf.hash) return false;
	// First reroot and then check the diff path from one to another
	p_arr::reroot(parent_s, arr_pt);
	weak_ptr<p_arr> diff_pt = uf.arr_pt;

	vector<pair<int_t, int_t>> diffs;
	while (diff_pt.lock()->diff != nullptr) {
		auto el = make_pair(diff_pt.lock()->p, 0);
		if (!binary_search(diffs.begin(), diffs.end(), el)) {
			diffs.emplace_back(move(el));
			sort(diffs.begin(), diffs.end());
		}
		//if(find(uf, diff_pt.lock()->p) != find(*this, arr_pt->p)) return false;
		diff_pt = diff_pt.lock()->diff;
	}
	for (auto &el: diffs) {
		el.second = find(*this, el.first);
	}
	return all_of(diffs.begin(), diffs.end(),
		      [&](pair<int_t, int_t> &el) {
			  return find(uf, el.first) == el.second;
		      });
}

template<typename T>
basic_ostream<T> PersistentUnionFind::print(int_t uf, basic_ostream<T> &os) {
	auto &t = uf_univ[uf];
	for (int_t i = 0; i < (int_t) p_arr::size(parent_s); ++i) {
		os << i << " ";
	}
	os << endl;
	for (int_t i = 0; i < (int_t) p_arr::size(parent_s); ++i) {
		os << p_arr::get(parent_s, t.arr_pt, i) << " ";
	}
	os << endl;
	for (int_t i = 0; i < (int_t) p_arr::size(parent_s); ++i) {
		os << p_arr::get(hashes_s, t.hash_pt, i) << " ";
	}
	os << endl << "Hash: " << t.hash << endl;
	os << endl << endl;
}

//Returns a vector of all equal elements to x including x in t
std::vector<int_t> PersistentUnionFind::get_equal(int_t t, int_t x) {
	auto &uf = uf_univ[t];
	int_t rep_x = find(uf, x);

	vector<int_t> set{};
	bool negate = false;
	//Go down linked list and negate rest of chain if - is encountered
	int_t next = rep_x;
	do {
		if (next < 0) negate = !negate;
		next = p_arr::get(link_s, uf.link_pt, abs(next));
		set.push_back(negate ? -next : next);
	} while (abs(next) != abs(rep_x));
	return set;
}

// Removes the set of equal elements from t
int_t PersistentUnionFind::rm_equal(int_t t, int_t x) {
	auto reset = [&](int_t pos, puf &uf) {
	    uf.arr_pt = p_arr::set(parent_s, uf.arr_pt, pos, pos);
	    uf.link_pt = p_arr::set(link_s, uf.link_pt, pos, pos);
	    uf.hash_pt = p_arr::set(hashes_s, uf.hash_pt, pos, 0);
	};

	//Create copy of current union find and remove from their
	auto uf = uf_univ[t];
	int_t rep_x = find(uf, x);
	int_t hash_rm = p_arr::get(hashes_s, uf.hash_pt, abs(rep_x));
	// Nothing to remove
	if (abs(rep_x) == abs(p_arr::get(link_s, uf.link_pt, abs(rep_x))))
		return t;

	int_t next = rep_x;
	do {
		int_t tmp = p_arr::get(link_s, uf.link_pt, abs(next));
		reset(abs(next), uf);
		next = tmp;
	} while (abs(rep_x) != abs(next));
	uf.hash -= hash_rm;

	return add(uf);
}

bool PersistentUnionFind::resize(int_t n) {
	if (p_arr::size(parent_s) <= n) return false;

	p_arr::resize(parent_s, n, [](int_t i) { return i; });
	p_arr::resize(link_s, n, [](int_t i) { return i; });
	p_arr::resize(hashes_s, n, [](int_t i) { return 0; });
	return true;
}

int_t PersistentUnionFind::size() {
	return p_arr::size(parent_s);
}

bool PersistentSet::operator==(const PersistentSet &s) const {
	return e == s.e && n == s.n;
}

int_t PersistentSet::add(int_t e, int_t n) {
	PersistentSet set = PersistentSet(e, n);
	if (auto it = set_memo.find(set); it != set_memo.end())
		return it->second;
	else
		return set_memo.emplace(set,
					set_univ.size()), set_univ.emplace_back(
			set), (int_t) set_univ.size() - 1;
}

bool PersistentSet::empty(int_t set_id) {
	return set_id == 0;
}

void PersistentSet::init() {
	set_univ.emplace_back(PersistentSet(0, 0));
	set_memo.emplace(PersistentSet(0, 0), 0);
}

int_t PersistentSet::next(int_t set_id) {
	return set_univ[set_id].n;
}

bool PersistentSet::contains(int_t set_id, int_t elem) {
	while (set_id != 0) {
		if (set_univ[set_id].e == elem) return true;
		set_id = next(set_id);
	}
	return false;
}

int_t PersistentSet::insert(int_t set_id, int_t elem) {
	if (auto it = set_cache.find(make_pair(set_id, elem)); it !=
							       set_cache.end())
		return it->second;
	int_t el = set_univ[set_id].e;
	if (el == elem) return set_id;

	int_t r;
	if (abs(el) == abs(elem)) r = 0;
	else if (abs_cmp(el, elem)) r = add(elem, set_id);
	else r = add(el, insert(set_univ[set_id].n, elem));

	set_cache.emplace(make_pair(set_id, elem), r);
	return r;
}

int_t PersistentSet::remove(int_t set_id, int_t elem) {
	int_t el = set_univ[set_id].e;
	if (el == elem) return set_univ[set_id].n;
		// In this case the element does not belong to the set
	else if (abs_cmp(el, elem)) return set_id;
	else return add(el, remove(set_univ[set_id].n, elem));
}

PersistentSet PersistentSet::get(int_t set_id) {
	return set_univ[set_id];
}

void PersistentSet::print(int_t set_id) {
	std::cout << "{";
	while (set_id != 0) {
		std::cout << set_univ[set_id].e;
		set_id = next(set_id);
		if (set_id != 0) std::cout << ", ";
	}
	std::cout << "}" << std::endl << std::endl;
}

int_t PersistentSet::find(int_t set_id, int_t elem) {
	while (set_id != 0) {
		if (set_univ[set_id].e == elem) return set_id;
		set_id = next(set_id);
	}
	return 0;
}


bool PersistentPairs::operator==(const PersistentPairs &p) const {
	return (e == p.e && n == p.n);
}

// Canonicity with negation is ensured by having the larger variable first
int_t PersistentPairs::add(pair<int_t, int_t> &e, int_t n) {
	PersistentPairs pair = PersistentPairs(form(e), n);
	if (auto it = pair_memo.find(pair); it != pair_memo.end())
		return it->second;
	else
		return pair_memo.emplace(pair,
					 pairs_univ.size()), pairs_univ.emplace_back(
			pair), (int_t) pairs_univ.size() - 1;
}

void PersistentPairs::init() {
	pairs_univ.emplace_back(PersistentPairs({0, 0}, 0));
	pair_memo.emplace(PersistentPairs({0, 0}, 0), 0);
}

int_t PersistentPairs::insert(int_t set_id, pair<int_t, int_t> &elem) {
	elem = form(elem);
	if (auto it = pair_cache.find(pair(set_id, elem)); it !=
							   pair_cache.end())
		return it->second;
	int_t r;
	auto &el = pairs_univ[set_id].e;
	if (el == elem) r = set_id;
	else if (abs_lex_cmp(el, elem)) r = add(elem, set_id);
	else r = add(el, insert(pairs_univ[set_id].n, elem));

	pair_cache.emplace(pair(set_id, elem), r);
	return r;
}

int_t PersistentPairs::insert(int_t set_id, int_t fst, int_t snd) {
	auto elem = pair(fst, snd);
	return insert(set_id, elem);
}

int_t PersistentPairs::remove(int_t set_id, pair<int_t, int_t> &elem) {
	elem = form(elem);
	auto &el = pairs_univ[set_id].e;
	if (el == elem) return pairs_univ[set_id].n;
		// In this case the element does not belong to the set
	else if (abs_lex_cmp(el, elem)) return set_id;
	else return add(el, remove(pairs_univ[set_id].n, elem));
}

bool PersistentPairs::empty(int_t set_id) {
	return set_id == 0;
}

bool PersistentPairs::contains(int_t set_id, pair<int_t, int_t> &elem) {
	elem = form(elem);
	while (set_id != 0) {
		if (pairs_univ[set_id].e == elem) return true;
		set_id = next(set_id);
	}
	return false;
}

std::vector<int_t> PersistentPairs::implies(int_t set_id, int_t elem) {
	vector<int_t> imp;
	while (set_id != 0) {
		auto &p = pairs_univ[set_id].e;
		if (p.first == elem) imp.emplace_back(p.second);
		else if (-p.second == elem) imp.emplace_back(-p.first);
		set_id = next(set_id);
	}
	return imp;
}

int_t PersistentPairs::next(int_t set_id) {
	return pairs_univ[set_id].n;
}

PersistentPairs PersistentPairs::get(int_t set_id) {
	return pairs_univ[set_id];
}

void PersistentPairs::print(int_t set_id) {
	std::cout << "{";
	while (set_id != 0) {
		auto &p = pairs_univ[set_id].e;
		std::cout << "{" + to_string(p.first) + "," +
			     to_string(p.second) + "}";
		set_id = next(set_id);
		if (set_id != 0) std::cout << ", ";
	}
	std::cout << "}" << std::endl << std::endl;
}

pair<int_t, int_t> PersistentPairs::form(pair<int_t, int_t> &p) {
	return abs_cmp(p.first, -p.second) ? move(
		make_pair(-p.second, -p.first)) : move(p);
}

std::vector<std::pair<int_t, int_t>> poset::eq_lift_hi;
std::vector<std::pair<int_t, int_t>> poset::eq_lift_lo;

void poset::lift_imps(poset &p, poset &hi, poset &lo) {
	int_t h = hi.imps;
	int_t l = lo.imps;
	auto h_imp = pp::get(hi.imps).e;
	auto l_imp = pp::get(lo.imps).e;

	while (h != 0 || l != 0) {
		if (h == l) {
			// All implications are contained in both
			while (h != 0) {
				insert_imp(p, h_imp);
				h = pp::next(h);
				h_imp = pp::get(h).e;
			}
			return;
		} else if (l == 0 || (l != 0 && abs_lex_cmp(l_imp, h_imp))) {
			if (ps::contains(lo.vars, -h_imp.first)) {
				// Implication is true in lo since antecedent is violated
				insert_imp(p, h_imp);
			} else if (ps::contains(lo.vars, h_imp.second) ||
				   pu::equal(lo.eqs, h_imp.first,
					     h_imp.second)) {
				// Implication is trivially true in lo or contained in equality
				insert_imp(p, h_imp);
			} else p.pure = false;
			h = pp::next(h);
			h_imp = pp::get(h).e;
		} else if (h == 0 || abs_lex_cmp(h_imp, l_imp)) {
			if (ps::contains(hi.vars, -l_imp.first)) {
				// Implication is true in hi since antecedent is violated
				insert_imp(p, l_imp);
			} else if (ps::contains(hi.vars, l_imp.second) ||
				   pu::equal(hi.eqs, l_imp.first,
					     l_imp.second)) {
				// Implication is trivially true in hi or contained in equality
				insert_imp(p, l_imp);
			} else p.pure = false;
			l = pp::next(l);
			l_imp = pp::get(l).e;
		} else {
			// Implication is contained in lo and hi
			insert_imp(p, h_imp);
			h = pp::next(h);
			l = pp::next(l);
			h_imp = pp::get(h).e;
			l_imp = pp::get(l).e;
		}
	}
}

void poset::lift_vars(poset &p, int_t v, poset &hi, poset &lo) {
	int_t h = hi.vars;
	int_t l = lo.vars;
	int_t h_var = ps::get(h).e;
	int_t l_var = ps::get(l).e;

	while (h != 0 || l != 0) {
		if (h == l) {
			// hi and lo have the same vars
			while (h != 0) {
				insert_var(p, h_var, true);
				h = ps::next(h);
				h_var = ps::get(h).e;
			}
			return;
		} else if (l == 0 || (h != 0 && abs(l_var) < abs(h_var))) {
			// Variable in hi but not in lo
			eq_lift_lo.emplace_back(pu::find(lo.eqs, h_var), h_var);
			h = ps::next(h);
			h_var = ps::get(h).e;
		} else if (h == 0 || abs(h_var) < abs(l_var)) {
			eq_lift_hi.emplace_back(pu::find(hi.eqs, l_var), l_var);
			// Here implications for the transitive closure have to be added.
			// But we want transitive reduction, therefore we don't add anything else.
			l = ps::next(l);
			l_var = ps::get(l).e;
		} else {
			// The absolute values of the variables are equal -> creates equality
			if (h_var == l_var) insert_var(p, h_var, true);
			else insert_eq(p, v, h_var);
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
void poset::lift_eqs(poset &p, int_t v, poset &hi, poset &lo) {
	auto pcomp =
		[&](pair<int_t, int_t> &p1, pair<int_t, int_t> &p2) {
		    return abs_cmp(p1.first, p2.first);
		};

	int_t hi_eq = hi.eqs;
	int_t lo_eq = lo.eqs;

	// Lifting of equalities due to variables
	sortc(eq_lift_hi, pcomp);
	sortc(eq_lift_lo, pcomp);
	for (auto i = 0; i < eq_lift_hi.size() - 1; ++i) {
		if (eq_lift_hi[i].first == eq_lift_hi[i + 1].first) {
			lo_eq = pu::merge(lo_eq, eq_lift_hi[i].second,
					  eq_lift_hi[i + 1].second);
		} else if (i == 0 ||
			   (eq_lift_hi[i - 1].first != eq_lift_hi[i].first)) {
			// Single variable is not part of an equality
			insert_imp(p, -v, eq_lift_hi[i].second);
		}
	}
	for (auto i = 0; i < eq_lift_lo.size() - 1; ++i) {
		if (eq_lift_lo[i].first == eq_lift_lo[i + 1].first) {
			hi_eq = pu::merge(hi_eq, eq_lift_lo[i].second,
					  eq_lift_lo[i + 1].second);
		} else if (i == 0 ||
			   eq_lift_lo[i - 1].first != eq_lift_lo[i].first) {
			// Single variable is not part of an equality
			insert_imp(p, v, eq_lift_lo[i].second);
		}
	}

	if (hi_eq == lo_eq) {
		// All equalities are lifted
		p.eqs = hi_eq;
	} else if (hi_eq != 0 && lo_eq != 0) {
		// Lifting of equalities contained in hi and lo
		p.eqs = pu::intersect(hi_eq, lo_eq);
		p.pure = false;
	}
}

poset poset::lift(int_t v, poset &hi, poset &lo) {
	poset p;
	// Check if p can possibly be pure
	if (hi.pure && lo.pure) p.pure = true;
	eq_lift_hi.clear();
	eq_lift_lo.clear();
	lift_imps(p, hi, lo);
	lift_vars(p, v, hi, lo);
	lift_eqs(p, v, hi, lo);
	return p;
}

/*
// Get resulting poset when assigning v
//TODO: return false
poset poset::eval(int_t v) {
  if (hasbc(true_var, v, abs_cmp())) {
    // remove v from true_var
    // check if poset is empty -> return T
    // else return *this with v removed
    poset res;
    res = *this;
    auto it = getbc(res.true_var, v, abs_cmp());
    res.true_var.erase(it);
    if(res.is_empty()) res.set_pure();
    return res.calc_hash(), res;
  }
  else if(hasbc(true_var, -v, abs_cmp())){
    // return F
    poset res;
    return res;
  }
  poset res;
  res.true_var = true_var;
  res.insert_true_var(v); // temporarily insert v
  res.eq_var = eq_var; // delete used equalities later
  // Check if v is part of some equality
  auto eq_set = eq_var.get_set(v);
  res.eq_var.delete_set(v);
  if(eq_set.size() > 1) {
    for(const auto& e : eq_set) res.insert_true_var(e);
  }
  // complete true_var set of res, possible due to transitive closure
  for(auto imp = imp_var.begin(); imp != imp_var.end(); ++imp) {
    // Antecedent of implication is true
    if(hasbc(res.true_var, imp->first, abs_cmp())) {
      res.insert_true_var(imp->second);
      // Ensure that equalities are used
      eq_set = res.eq_var.get_set(imp->second);
      res.eq_var.delete_set(imp->second);
      if (eq_set.size() > 1)
        for (const auto &e: eq_set)
          res.insert_true_var(e);
    }
    // Check if a consequent is already true
    else if (hasbc(res.true_var, -imp->second, abs_cmp())) {
      res.insert_true_var(-imp->first);
      // Ensure that equalities are used
      eq_set = res.eq_var.get_set(-imp->first);
      res.eq_var.delete_set(-imp->first);
      if (eq_set.size() > 1)
        for (const auto &e: eq_set)
          res.insert_true_var(e);
    }
  }
  // delete all implications where at least one variable
  // (in absolute value) appears in true_var
  for(auto imp = imp_var.begin(); imp != imp_var.end(); ++imp) {
    if (!hasbc(res.true_var, imp->first, abs_cmp())
        && !hasbc(res.true_var, -imp->first, abs_cmp())){
      // negated antecedent is already in true_var
      DBG(assert(!hasbc(res.true_var, -imp->second, abs_cmp()));)
      if (!hasbc(res.true_var, imp->second, abs_cmp())) {
        res.insert_implication(*imp);
      }
    }
  }
  // v was only temporarily added
  res.true_var.erase(getbc(res.true_var, v, abs_cmp()));
  res.set_pure();
  return res.calc_hash(), res;
}
*/

bool poset::insert_var(poset &p, int_t v, bool val) {
	return val ? p.vars = ps::insert(p.vars, v) :
		p.vars = ps::insert(p.vars, -v);
}

void poset::insert_imp(poset &p, std::pair<int_t, int_t> &el) {
	p.imps = pp::insert(p.imps, el);
}

void poset::insert_imp(poset &p, int_t fst, int_t snd) {
	p.imps = pp::insert(p.imps, fst, snd);
}

void poset::insert_eq(poset &p, int_t v1, int_t v2) {
	p.eqs = pu::merge(p.eqs, v1, v2);
}

poset poset::get(int_t pos, bool negated) {
	return negated ?
	       (pos > 0 ? NP[pos] : P[-pos]) :
	       (pos > 0 ? P[pos] : NP[-pos]);
}

bool poset::operator==(const poset &p) const {
	return p.vars == vars && p.imps == imps &&
		p.eqs == eqs && p.pure == pure;
}











