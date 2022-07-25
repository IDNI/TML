#include "poset.h"
#include <numeric>

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

auto abs_fst_cmp = [](auto &p1, auto &p2) {
    return abs_cmp(p1.first, p2.first);
};

// universe for positively saved posets
vector<poset> P;
// universe for negatively saved posets
vector<poset> NP;

std::vector<PersistentArray> pa_univ;
std::vector<PersistentUnionFind> uf_univ;
std::vector<PersistentPairs> pairs_univ;
std::vector<PersistentSet> set_univ;
std::unordered_map<PersistentUnionFind, int_t> uf_memo;
std::unordered_map<PersistentPairs, int_t> pair_memo;
std::unordered_map<PersistentSet, int_t> set_memo;

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

int_t PersistentArray::init(storage &arr, int_t n,
			   std::function<int_t(int_t)> &&f) {
	pa_univ.emplace_back();
	if (!arr.empty()) return -1;
	arr.reserve(n);
	for (int_t i = 0; i < n; ++i) arr.emplace_back(f(i));
	return 0;

}

int_t PersistentArray::get(storage &arr, int_t &c, int_t t, int_t pos,
			   bool reset_to_num) {
	if (t == c) {
		// Here we operate directly on the vector
		return arr[pos];
	}
	reroot(arr, c, t, reset_to_num);
	return arr[pos];
}

int_t
PersistentArray::set(storage &arr, int_t &c, int_t t, int_t pos, int_t val,
		     bool reset_to_num) {
	reroot(arr, c, t, reset_to_num);
	if (get(arr, c, t, pos, reset_to_num) == val) return t;

	arr[pos] = val;
	pa_univ.emplace_back(pos, val, t);
	c = (int) pa_univ.size() - 1;
	return c;
}

void PersistentArray::reroot(storage &arr, int_t& c, int_t t, bool reset_to_num) {
	if(t == c) return;

	// Undo diff chain from c
	while(pa_univ[c].diff != -1) {
		if(c == t) {
			update(arr, t);
			return;
		}
		if(reset_to_num)
			arr[pa_univ[c].p] = pa_univ[c].p;
		else arr[pa_univ[c].p] = 0;
		c = pa_univ[c].diff;
	}

	update(arr, t);
	c = t;
}

void PersistentArray::update(storage &arr, int t) {
	if (pa_univ[t].diff == -1) return;
	update(arr, pa_univ[t].diff);

	arr[pa_univ[t].p] = pa_univ[t].v;
}

vector<int_t> PersistentUnionFind::parent_s;
vector<int_t> PersistentUnionFind::link_s;
vector<int_t> PersistentUnionFind::hashes_s;

int_t PersistentUnionFind::current_parent;
int_t PersistentUnionFind::current_link;
int_t PersistentUnionFind::current_hash;

void PersistentUnionFind::init(int_t n) {
	if (!uf_univ.empty()) return;
	pu root = pu(n);
	uf_univ.push_back(root);
	uf_memo.try_emplace(root, 0);
}

int_t PersistentUnionFind::find(const pu &t, int_t elem) {
	auto t_elem = pa::get(parent_s, current_parent, t.arr_pt, abs(elem),
			      true);
	if (abs(t_elem) == abs(elem)) return elem < 0 ? -t_elem : t_elem;
	else {
		auto r = elem < 0 ? -find(t, t_elem) : find(t, t_elem);
		t.arr_pt = pa::set(parent_s, current_parent, t.arr_pt,
				   abs(elem),
				   elem < 0 ? -r : r, true);
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
int_t PersistentUnionFind::update(const pu &t, int_t x, int_t y) {
	DBG(assert(y >= 0));
	auto hash_x = pa::get(hashes_s, current_hash, t.hash_pt, abs(x), false);
	auto hash_y = pa::get(hashes_s, current_hash, t.hash_pt, y, false);
	auto uf = pu(pa::set(parent_s, current_parent, t.arr_pt, abs(x),
			     x < 0 ? -y : y, true),
		     update_link(t, x, y),
		     pa::set(hashes_s, current_hash, t.hash_pt, y,
			     hash_set(x, y, hash_x, hash_y), false),
		     t.hash, x, y, hash_x, hash_y);
	return add(uf);
}

int_t PersistentUnionFind::add(pu &uf) {
	if (auto it = uf_memo.find(uf); it != uf_memo.end()) {
		return it->second;
	} else {
		uf_univ.push_back(uf);
		uf_memo.try_emplace(uf, uf_univ.size() - 1);
		return (int_t) uf_univ.size() - 1;
	}
}

/*void
PersistentUnionFind::split_set(vector<int_t> &s, PersistentUnionFind::pu &uf,
			       int_t root) {
	if (s.empty()) return;
	for (auto el: s) {
		uf.arr_pt = pa::set(parent_s, uf.arr_pt, abs(el),
				       el < 0 ? -s[0] : s[0]);
	}
	split_linking(s, uf, abs(root));
}

void PersistentUnionFind::split_hashes(int_t root_x, int_t root_y, int_t hash_x,
				       int_t hash_y, int_t count_x,
				       int_t count_y,
				       int_t prev_root, puf &uf) {
	int_t prev_hash = p_arr::get(hashes_s, uf.hash_pt, abs(prev_root));
	DBG(assert(!(count_x > 1 && count_y > 1) ||
		   (hash_x + hash_y == prev_hash));)
	if (count_x > 1)
		uf.hash_pt = p_arr::set(hashes_s, uf.hash_pt, root_x, hash_x);
	if (count_y > 1)
		uf.hash_pt = p_arr::set(hashes_s, uf.hash_pt, root_y, hash_y);
	uf.hash = uf.hash ^ prev_hash ^ (count_x > 1 ? hash_x : 0) ^
		  (count_y > 1 ? hash_y : 0);
}

void
PersistentUnionFind::split_linking(std::vector<int_t> &s, puf &uf, int_t root) {
	int_t hash_cs = 0, root_cs = 0, count_cs = 0;
	int_t hash_s = 0;
	bool inv = false;
	// Remove set s from linking
	int_t x = root;
	int_t y = p_arr::get(link_s, uf.link_pt, root);
	while (abs(y) != root) {
		inv = y < 0;
		if (hasbc(s, y, abs_cmp) || hasbc(s, -y, abs_cmp)) {
			y = p_arr::get(link_s, uf.link_pt, abs(y));
			y = inv ? -y : y;
			uf.link_pt = p_arr::set(link_s, uf.link_pt, x, y);
		} else {
			hash_cs += y * y;
			++count_cs;
			if (root_cs == 0) root_cs = abs(y);

			x = abs(y);
			y = p_arr::get(link_s, uf.link_pt, abs(y));
			y = inv ? -y : y;
		}
	}
	if (hasbc(s, y, abs_cmp) || hasbc(s, -y, abs_cmp)) {
		inv = y < 0;
		y = p_arr::get(link_s, uf.link_pt, abs(y));
		y = inv ? -y : y;
		uf.link_pt = p_arr::set(link_s, uf.link_pt, x, y);
	} else {
		root_cs = abs(y);
		++count_cs;
		hash_cs += y * y;
	}

	// Introduce linking for set s
	inv = false;
	for (int_t i = 0; i + 1 < (int_t) s.size(); ++i) {
		uf.link_pt = p_arr::set(link_s, uf.link_pt, abs(s[i]),
					inv ? -s[i + 1] : s[i + 1]);
		if ((s[i] < 0 && s[i + 1] > 0) || (s[i] > 0 && s[i + 1] < 0))
			inv = !inv;
		hash_s += s[i + 1] * s[i + 1];
	}
	uf.link_pt = p_arr::set(link_s, uf.link_pt, abs(s[s.size() - 1]),
				inv ? -s[0] : s[0]);
	hash_s += s[0] * s[0];

	split_hashes(abs(s[0]), root_cs, hash_s, hash_cs, (int_t) s.size(),
		     count_cs, root, uf);
}
*/

int_t PersistentUnionFind::update_link(const pu &t, int_t x, int_t y) {
	// y is the new parent of x
	DBG(assert(y >= 0));
	int_t y_link = pa::get(link_s, current_link, t.link_pt, y, true);
	int_t x_link = pa::get(link_s, current_link, t.link_pt, abs(x), true);

	auto link1 = pa::set(link_s, current_link, t.link_pt, y,
			     x < 0 ? -x_link : x_link, true);
	return pa::set(link_s, current_link, link1, abs(x),
		       x < 0 ? -y_link : y_link, true);
}

pu_iterator PersistentUnionFind::HalfList(const pu_iterator &start,
					  const pu_iterator &end) {
	pu_iterator fast(start);
	pu_iterator slow(start);

	while (fast != end) {
		++fast;
		if (fast != end) {
			++fast;
			++slow;
		}
	}
	return slow;
}

int_t PersistentUnionFind::SortedMerge(pu_iterator &a, pu_iterator &b,
				       int_t a_end, int_t b_end,
				       int_t pos, bool negated) {
	auto set_pos = [&](int_t v) {
	    pos = negated ? -v : v;
	    if (pos < 0) negated = !negated;
	};

	if (abs(*a) == abs(a_end)) {
		a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt, abs(pos),
					  negated ? -*b : *b, true);
		set_pos(*b);
		while (abs(*(++b)) != abs(b_end)) {
			a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt,
						  abs(pos), negated ? -*b : *b, true);
			set_pos(*b);
		}
		return 0;
	} else if (abs(*b) == abs(b_end)) {
		a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt, abs(pos),
					  negated ? -*a : *a, true);
		set_pos(*a);
		while (abs(*(++a)) != abs(a_end)) {
			a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt,
						  abs(pos), negated ? -*a : *a, true);
			set_pos(*a);
		}
		//Correcting end value of chain
		a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt, abs(pos),
					  negated ? -b_end : b_end, true);
		return 0;
	}

	if (abs_cmp(*a, *b)) {
		if (pos == 0) {
			set_pos(*a);
			return SortedMerge(++a, b, a_end, b_end, pos, negated);
		} else {
			a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt,
						  abs(pos), negated ? -*a : *a, true);
			set_pos(*a);
			return SortedMerge(++a, b, a_end, b_end, pos, negated);
		}
	} else {
		if (pos == 0) {
			set_pos(*b);
			SortedMerge(a, ++b, a_end, b_end, pos, negated);
			// Start position changed
			return pos;
		} else {
			a.uf.link_pt = pa::set(pu::link_s, current_link, a.uf.link_pt,
						  abs(pos), negated ? -*b : *b, true);
			set_pos(*b);
			return SortedMerge(a, ++b, a_end, b_end, pos, negated);
		}
	}
}

int_t
PersistentUnionFind::MergeSort(pu_iterator start, const pu_iterator &end) {
	if (start == end) return 0;

	pu_iterator mid(HalfList(start, end));
	if (mid == start) return 0;

	int_t mid_val = *mid;
	int_t start_update = 0;
	if (start_update = MergeSort(start, mid); abs(start_update) > 0) {
		//update start position
		start.update_pos(start_update);
	}
	if (int_t i = MergeSort(mid, end); abs(i) > 0) {
		//update start position
		mid.update_pos(i);
	}

	if (int_t res = SortedMerge(start, mid, mid_val, *end, 0, false);
		res == 0)
		return start_update;
	else
		return res;
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
	auto cx = pu::find(uf, x);
	auto cy = pu::find(uf, y);
	form(cx, cy);
	if (cx != cy) {
		if (abs(cy) < abs(cx)) return update(uf, cx, cy);
		else
			assert(false);
		return 0;
	} else return t;
}

int_t PersistentUnionFind::merge_set(int_t t, std::vector<int_t> &s) {
	if (s.size()<2) return t;
	for (int_t i = 1; i < (int_t)s.size(); ++i) {
		t = merge(t, s[0], s[i]);
	}
	return t;
}

int_t PersistentUnionFind::intersect(int_t t1, int_t t2) {
	if (t1 == t2) return t1;
	else if (t1 == 0 || t2 == 0) return 0;

	auto &uf1 = uf_univ[t1];
	auto &uf2 = uf_univ[t2];

	int_t diff_pt = uf1.arr_pt;
	int_t result = 0;
	static unordered_map<pair<int_t, int_t>, int_t> classes;
	static set<pair<int_t,int_t>> diffs;

	while (pa_univ[diff_pt].diff != -1) {
		diffs.emplace(pa_univ[diff_pt].p, find(uf1, pa_univ[diff_pt].p));
		diff_pt = pa_univ[diff_pt].diff;
	}
	for (auto& el : diffs) {
		if (auto iter = classes.find({el.second, find(uf2, el.first)});
			iter != classes.end()) {
			result = merge(result, el.first, iter->second);
		} else {
			classes.emplace(pair(el.second, find(uf2, el.first)), el.first);
		}
	}
	classes.clear();
	diffs.clear();
	return result;
}

bool PersistentUnionFind::equal(int_t t, int_t x, int_t y) {
	auto &uf = uf_univ[t];
	return find(uf, x) == find(uf, y);
}

bool PersistentUnionFind::operator==(const pu &uf) const {
	//Quickcheck hashes
	if (hash != uf.hash) return false;

	int_t diff_pt = arr_pt;
	static set<pair<int_t,int_t>> diffs;
	diffs.clear();

	while (pa_univ[diff_pt].diff != -1) {
		diffs.emplace(pa_univ[diff_pt].p, find(*this, pa_univ[diff_pt].p));
		diff_pt = pa_univ[diff_pt].diff;
	}
	diff_pt = uf.arr_pt;
	pair<int_t,int_t> tmp_pair;
	while (pa_univ[diff_pt].diff != -1) {
		tmp_pair.first = pa_univ[diff_pt].p;
		tmp_pair.second = find(uf, pa_univ[diff_pt].p);
		if (auto iter = diffs.find(tmp_pair); iter != diffs.end()) {
			diffs.erase(iter);
		} else if(tmp_pair.first != tmp_pair.second) return false;
		diff_pt = pa_univ[diff_pt].diff;
	}
	return all_of(all(diffs), [](auto &p) { return p.first == p.second; });
}

void PersistentUnionFind::print(int_t uf, ostream &os) {
	auto &t = uf_univ[uf];
	print(t, os);
}

//Returns a vector of all equal elements to x including x in t
pu_iterator PersistentUnionFind::get_equal(int_t t, int_t x) {
	auto &uf = uf_univ[t];
	return get_equal(uf, x);
}

// Removes the set of equal elements from t
int_t PersistentUnionFind::rm_equal(int_t t, int_t x) {
	auto reset = [&](int_t pos, pu &uf) {
	    uf.arr_pt = pa::set(parent_s, current_parent, uf.arr_pt, pos, pos, true);
	    uf.link_pt = pa::set(link_s, current_link, uf.link_pt, pos, pos, true);
	    uf.hash_pt = pa::set(hashes_s, current_hash, uf.hash_pt, pos, 0, false);
	};

	//Create copy of current union find and remove from their
	auto uf = uf_univ[t];
	int_t rep_x = find(uf, x);
	// Nothing to remove
	if (abs(rep_x) == abs(pa::get(link_s, current_link, uf.link_pt, abs(rep_x), true)))
		return t;

	int_t hash_rm = pa::get(hashes_s, current_hash, uf.hash_pt, abs(rep_x), false);
	int_t next = rep_x;
	do {
		int_t tmp = pa::get(link_s, current_link, uf.link_pt, abs(next), true);
		reset(abs(next), uf);
		next = tmp;
	} while (abs(rep_x) != abs(next));
	uf.hash ^= hash_rm;

	return add(uf);
}

bool PersistentUnionFind::resize(int_t n) {
	if (pa::size(parent_s) > n) return false;

	pa::resize(parent_s, n, [](int_t i) { return i; });
	pa::resize(link_s, n, [](int_t i) { return i; });
	pa::resize(hashes_s, n, [](int_t i) { return 0; });
	return true;
}

int_t PersistentUnionFind::size() {
	return pa::size(parent_s);
}

pu_iterator
PersistentUnionFind::get_equal(PersistentUnionFind::pu &uf, int_t x) {
	int_t rep_x = find(uf, x);
	return {uf, rep_x};
}

void PersistentUnionFind::print(PersistentUnionFind::pu &uf, ostream &os) {
	for (int_t i = 0; i < (int_t) pa::size(parent_s); ++i) {
		os << i << " ";
	}
	os << endl;
	for (int_t i = 0; i < (int_t) pa::size(parent_s); ++i) {
		os << pa::get(parent_s, current_parent, uf.arr_pt, i, true) << " ";
	}
	os << endl;
	for (int_t i = 0; i < (int_t) pa::size(link_s); ++i) {
		os << pa::get(link_s, current_link, uf.link_pt, i, true) << " ";
	}
	os << endl;
	for (int_t i = 0; i < (int_t) pa::size(hashes_s); ++i) {
		os << pa::get(hashes_s, current_hash, uf.hash_pt, i, false) << " ";
	}
	os << endl << "Hash: " << uf.hash << endl;
	os << endl;
}

bool PersistentSet::operator==(const PersistentSet &s) const {
	return e == s.e && n == s.n;
}

int_t PersistentSet::add(int_t e, int_t n) {
	PersistentSet set = PersistentSet(e, n);
	if (auto it = set_memo.find(set); it != set_memo.end())
		return it->second;
	else
		return set_memo.emplace(set, set_univ.size()),
			set_univ.emplace_back(set), (int_t) set_univ.size() - 1;
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
	//if (auto it = set_cache.find(make_pair(set_id, elem)); it !=
							       //set_cache.end())
	//	return it->second;
	int_t el = set_univ[set_id].e;
	if (el == elem) return set_id;

	int_t r;
	if (abs(el) == abs(elem)) r = 0;
	else if (abs_cmp(elem, el) || el == 0) r = add(elem, set_id);
	else r = add(el, insert(set_univ[set_id].n, elem));

	//set_cache.emplace(make_pair(set_id, elem), r);
	return r;
}

int_t PersistentSet::remove(int_t set_id, int_t elem) {
	int_t el = set_univ[set_id].e;
	if (el == elem) return set_univ[set_id].n;
		// In this case the element does not belong to the set
	else if (abs_cmp(elem, el) || el == 0) return set_id;
	else return add(el, remove(set_univ[set_id].n, elem));
}

PersistentSet PersistentSet::get(int_t set_id) {
	return set_univ[set_id];
}

void PersistentSet::print(int_t set_id, ostream &os) {
	os << "{";
	while (set_id != 0) {
		os << set_univ[set_id].e;
		set_id = next(set_id);
		if (set_id != 0) os << ", ";
	}
	os << "}" << std::endl << std::endl;
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

// Canonicity with negation is ensured by having the smaller variable first
int_t PersistentPairs::add(pair<int_t, int_t> &e, int_t n) {
	PersistentPairs pair = PersistentPairs(form(e), n);
	if (auto it = pair_memo.find(pair); it != pair_memo.end())
		return it->second;
	else
		return pair_memo.emplace(pair,
					 pairs_univ.size()), pairs_univ.emplace_back(
			move(pair)), (int_t) pairs_univ.size() - 1;
}

void PersistentPairs::init() {
	pairs_univ.emplace_back(PersistentPairs({0, 0}, 0));
	pair_memo.emplace(PersistentPairs({0, 0}, 0), 0);
}

int_t PersistentPairs::insert(int_t set_id, pair<int_t, int_t> &elem) {
	elem = form(elem);
	/*if (auto it = pair_cache.find(pair(set_id, elem)); it !=
							   pair_cache.end())
		return it->second;*/
	int_t r;
	auto el = pairs_univ[set_id].e;

	if (el == elem) r = set_id;
	else if (abs_lex_cmp(elem, el) || (el.first == 0 && el.second == 0))
		r = add(elem, set_id);
	else r = add(el, insert(pairs_univ[set_id].n, elem));


	//pair_cache.emplace(pair(set_id, elem), r);
	return r;
}

int_t PersistentPairs::insert(int_t set_id, int_t fst, int_t snd) {
	auto elem = pair(fst, snd);
	return insert(set_id, elem);
}

int_t PersistentPairs::remove(int_t set_id, pair<int_t, int_t> &elem) {
	elem = form(elem);
	auto el = pairs_univ[set_id].e;
	if (el == elem) return pairs_univ[set_id].n;
		// In this case the element does not belong to the set
	else if (abs_lex_cmp(elem, el) ||
		 (el.first == 0 && el.second == 0))
		return set_id;
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

int_t PersistentPairs::implies(int_t set_id, int_t elem, bool del,
			       vector<int_t> &imp) {
	int_t id = set_id;
	while (set_id != 0) {
		auto &p = pairs_univ[set_id].e;
		if (p.first == elem) {
			imp.emplace_back(p.second);
			if (del) id = remove(id, p);
		} else if (-p.second == elem) {
			imp.emplace_back(-p.first);
			if (del) id = remove(id, p);
		} else if (p.first == -elem || p.second == elem) {
			if (del) id = remove(id, p);
		}
		set_id = next(set_id);
	}
	return id;
}

int_t PersistentPairs::all_implies(int_t set_id, int_t elem, bool del,
				   vector<int_t> &all_imp) {
	if (set_id == 0) return 0;
	auto start = (int_t) all_imp.size();
	set_id = implies(set_id, elem, del, all_imp);
	auto end = (int_t) all_imp.size();
	for (int i = start; i < end; ++i) {
		set_id = all_implies(set_id, all_imp[i], del, all_imp);
	}
	return set_id;
}

int_t PersistentPairs::next(int_t set_id) {
	return pairs_univ[set_id].n;
}

PersistentPairs PersistentPairs::get(int_t set_id) {
	return pairs_univ[set_id];
}

void PersistentPairs::print(int_t set_id, ostream &os) {
	os << "{";
	while (set_id != 0) {
		auto &p = pairs_univ[set_id].e;
		os << "{" + to_string(p.first) + "," +
		      to_string(p.second) + "}";
		set_id = next(set_id);
		if (set_id != 0) os << ", ";
	}
	os << "}" << std::endl << std::endl;
}

pair<int_t, int_t> PersistentPairs::form(pair<int_t, int_t> &p) {
	return abs_cmp(-p.second, p.first) ?
	       move(pair(-p.second, -p.first)) : move(p);
}

std::unordered_map<int_t,int_t> poset::eq_lift_hi;
std::unordered_map<int_t,int_t> poset::eq_lift_lo;
std::vector<std::pair<int_t, int_t>> poset::eq_lift;

// Must be called after lift_vars due to initialization of eq_lift_hi/lo
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
		} else if (l == 0 || (h != 0 && abs_lex_cmp(h_imp, l_imp))) {
			if (ps::contains(lo.vars, -h_imp.first) ||
			    pu::equal(lo.eqs, h_imp.first, h_imp.second)) {
				// Implication is true in lo since antecedent is violated
				// or contained in equality
				insert_imp(p, h_imp);
			} else if (ps::contains(lo.vars, h_imp.second)) {
				// Implication is trivially true in lo or contained in equality
				insert_imp(p, h_imp);
				if (ps::contains(lo.vars, h_imp.first)) {
					//In this case v -> h_imp.second is not allowed to be lifted later
					eq_lift_hi.erase((abs_cmp(h_imp.first, h_imp.second)
							  ? h_imp.second : h_imp.first));
				}
			} else p.pure = false;
			h = pp::next(h);
			h_imp = pp::get(h).e;
		} else if (h == 0 || abs_lex_cmp(l_imp, h_imp)) {
			if (ps::contains(hi.vars, -l_imp.first) ||
			    pu::equal(hi.eqs, l_imp.first, l_imp.second)) {
				// Implication is true in hi since antecedent is violated
				insert_imp(p, l_imp);
			} else if (ps::contains(hi.vars, l_imp.second)) {
				// Implication is trivially true in hi or contained in equality
				insert_imp(p, l_imp);
				if (ps::contains(hi.vars, l_imp.first)) {
					//In this case v -> l_imp.second is not allowed to be lifted later
					eq_lift_lo.erase((abs_cmp(l_imp.first, l_imp.second)
							  ? l_imp.second : l_imp.first));
				}
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
void poset::lift_eqs(poset &p, int_t v, poset &hi, poset &lo) {
	auto pcomp =
		[&](pair<int_t, int_t> &p1, pair<int_t, int_t> &p2) {
		    return abs_cmp(p1.first, p2.first);
		};

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
	eq_lift_hi.clear();
	eq_lift_lo.clear();
	eq_lift.clear();
	lift_vars(p, v, hi, lo);
	lift_imps(p, hi, lo);
	lift_eqs(p, v, hi, lo);
	p.v = abs(v); // v must be the smallest variable in p
	return p;
}

// Evaluate poset on the variable v
//TODO: return false
//TODO: Update variable v in p
poset poset::eval(poset &p, int_t v) {
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

	static vector<int_t> all_imp;
	for (auto el: pu::get_equal(res.eqs, v)) {
		res.vars = ps::insert(res.vars, el);
		res.imps = pp::all_implies(res.imps, el, true, all_imp);
	}
	res.eqs = pu::rm_equal(res.eqs, v);
	for (int i = 0; i < (int) all_imp.size(); ++i) {
		for (auto el: pu::get_equal(res.eqs, all_imp[i])) {
			res.vars = ps::insert(res.vars, el);
			res.imps = pp::all_implies(res.imps, el, true, all_imp);
		}
		res.eqs = pu::rm_equal(res.eqs, all_imp[i]);
	}
	res.vars = ps::remove(res.vars, v);
	all_imp.clear();
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
	p.imps = pp::insert(p.imps, el);
}

void poset::insert_imp(poset &p, int_t fst, int_t snd) {
	if (abs(fst) < p.v || p.v == 0) p.v = abs(fst);
	if (abs(snd) < p.v || p.v == 0) p.v = abs(snd);
	p.imps = pp::insert(p.imps, fst, snd);
}

void poset::insert_eq(poset &p, int_t v1, int_t v2) {
	if (abs(v1) < p.v || p.v == 0) p.v = abs(v1);
	if (abs(v2) < p.v || p.v == 0) p.v = abs(v2);
	p.eqs = pu::merge(p.eqs, v1, v2);
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
	pp::print(p.imps, os);
	ps::print(p.vars, os);
}

void poset::print(poset &&p, ostream &os) {
	print(p, os);
}










