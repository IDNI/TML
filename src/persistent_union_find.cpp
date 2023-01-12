#include "persistent_union_find.h"

using namespace std;
using pu = persistent_union_find;
using pa = PersistentArray;

static std::vector<pa> pa_univ;
static std::vector<pu> uf_univ;
static std::unordered_map<pu, int_t> uf_memo;

namespace { abs_cmp_ abs_cmp; }

size_t std::hash<pu>::operator()(const pu &uf) const {
	return uf.hash;
}

size_t std::hash<std::pair<int_t, int_t>>::operator()(
	const std::pair<int_t, int_t> &p) const {
	return hash_pair(p.first, p.second);
}

int_t PersistentArray::init(storage &arr, int_t n, int_t(*f)(int_t)) {
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

vector<int_t> pu::parent_s;
vector<int_t> pu::link_s;
vector<int_t> pu::hashes_s;

int_t pu::current_parent;
int_t pu::current_link;
int_t pu::current_hash;

void pu::init(int_t n) {
	if (!uf_univ.empty()) return;
	pu root = pu(n);
	uf_univ.push_back(root);
	uf_memo.try_emplace(root, 0);
}

int_t pu::find(const pu &t, int_t elem) {
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

int_t pu::find(int_t t, int_t elem) {
	auto &uf = uf_univ[t];
	return find(uf, elem);
}

// Updates t by setting the value at x to y
// while assuming that x and y are root nodes
// y is the new parent of x
int_t pu::update(const pu &t, int_t x, int_t y) {
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

int_t pu::add(pu &uf) {
	if (auto it = uf_memo.find(uf); it != uf_memo.end()) {
		return it->second;
	} else {
		uf_univ.push_back(uf);
		uf_memo.try_emplace(uf, uf_univ.size() - 1);
		return (int_t) uf_univ.size() - 1;
	}
}

int_t pu::update_link(const pu &t, int_t x, int_t y) {
	// y is the new parent of x
	DBG(assert(y >= 0));
	int_t y_link = pa::get(link_s, current_link, t.link_pt, y, true);
	int_t x_link = pa::get(link_s, current_link, t.link_pt, abs(x), true);

	auto link1 = pa::set(link_s, current_link, t.link_pt, y,
			     x < 0 ? -x_link : x_link, true);
	return pa::set(link_s, current_link, link1, abs(x),
		       x < 0 ? -y_link : y_link, true);
}

pu_iterator pu::HalfList(const pu_iterator &start,
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

int_t pu::SortedMerge(pu_iterator &a, pu_iterator &b,
				       int_t a_end, int_t b_end,
				       int_t pos, bool negated) {
	auto set_pos = [&](int_t v) {
	    pos = negated ? -v : v;
	    if (pos < 0) negated = !negated;
	};

	pu& uf_a = uf_univ[a.t];
	if (abs(*a) == abs(a_end)) {
		uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt, abs(pos),
				       negated ? -*b : *b, true);
		set_pos(*b);
		while (abs(*(++b)) != abs(b_end)) {
			uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt,
					       abs(pos), negated ? -*b : *b, true);
			set_pos(*b);
		}
		return 0;
	} else if (abs(*b) == abs(b_end)) {
		uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt, abs(pos),
				       negated ? -*a : *a, true);
		set_pos(*a);
		while (abs(*(++a)) != abs(a_end)) {
			uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt,
					       abs(pos), negated ? -*a : *a, true);
			set_pos(*a);
		}
		//Correcting end value of chain
		uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt, abs(pos),
				       negated ? -b_end : b_end, true);
		return 0;
	}

	if (abs_cmp(*a, *b)) {
		if (pos == 0) {
			set_pos(*a);
			return SortedMerge(++a, b, a_end, b_end, pos, negated);
		} else {
			uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt,
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
			uf_a.link_pt = pa::set(pu::link_s, current_link, uf_a.link_pt,
					       abs(pos), negated ? -*b : *b, true);
			set_pos(*b);
			return SortedMerge(a, ++b, a_end, b_end, pos, negated);
		}
	}
}

int_t
pu::MergeSort(pu_iterator start, const pu_iterator &end) {
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

int_t pu::merge(int_t t, int_t x, int_t y) {
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

int_t pu::merge_set(int_t t, std::vector<int_t> &s) {
	if (s.size()<2) return t;
	for (int_t i = 1; i < (int_t)s.size(); ++i) {
		t = merge(t, s[0], s[i]);
	}
	return t;
}

int_t pu::intersect(int_t t1, int_t t2) {
	if (t1 == t2) return t1;
	else if (t1 == 0 || t2 == 0) return 0;

	const auto &uf1 = uf_univ[t1];
	const auto &uf2 = uf_univ[t2];

	int_t diff_pt = uf1.arr_pt;
	int_t result = 0;
	unordered_map<pair<int_t, int_t>, int_t> classes;
	set<pair<int_t,int_t>> diffs;

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
	return result;
}

bool pu::equal(int_t t, int_t x, int_t y) {
	auto &uf = uf_univ[t];
	return find(uf, x) == find(uf, y);
}

bool pu::operator==(const pu &uf) const {
	//Quickcheck hashes
	if (hash != uf.hash) return false;

	int_t diff_pt = arr_pt;
	map<pair<int_t,int_t>, bool> diffs;

	while (pa_univ[diff_pt].diff != -1) {
		diffs.emplace(pair(pa_univ[diff_pt].p, find(*this, pa_univ[diff_pt].p)), false);
		diff_pt = pa_univ[diff_pt].diff;
	}
	diff_pt = uf.arr_pt;
	pair<int_t,int_t> tmp_pair;
	while (pa_univ[diff_pt].diff != -1) {
		tmp_pair.first = pa_univ[diff_pt].p;
		tmp_pair.second = find(uf, pa_univ[diff_pt].p);
		if (auto iter = diffs.find(tmp_pair); iter != diffs.end()) {
			iter->second = true;
		} else if(tmp_pair.first != tmp_pair.second) return false;
		diff_pt = pa_univ[diff_pt].diff;
	}
	return all_of(all(diffs), [](auto &p) { return p.first.first == p.first.second || p.second == true; });
}

void pu::print(int_t uf, ostream &os) {
	auto &t = uf_univ[uf];
	print(t, os);
}

//Returns a vector of all equal elements to x including x in t
pu_iterator pu::get_equal(int_t t, int_t x) {
	auto &uf = uf_univ[t];
	return get_equal(uf, x);
}

// Removes the set of equal elements from t
int_t pu::rm_equal(int_t t, int_t x) {
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

bool pu::is_singleton(int_t t, int_t x) {
	auto set_iter = get_equal(t,x);
	++set_iter;
	return set_iter == set_iter.end();
}

bool pu::resize(int_t n) {
	if (pa::size(parent_s) > n) return false;

	pa::resize(parent_s, n, [](int_t i) { return i; });
	pa::resize(link_s, n, [](int_t i) { return i; });
	pa::resize(hashes_s, n, [](int_t i) { return 0; });
	return true;
}

int_t pu::size() {
	return pa::size(parent_s);
}

pu_iterator
pu::get_equal(pu::pu &uf, int_t x) {
	int_t rep_x = find(uf, x);
	return {uf_memo[uf], rep_x};
}

void pu::print(pu::pu &uf, ostream &os) {
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

pu_iterator &pu_iterator::operator++() {
	if (!looped) looped = true;
	val = pa::get(pu::link_s, pu::current_link, uf_univ[t].link_pt, abs(val), true);
	val = negate ? -val : val;
	if ((negate ? -val : val) < 0) negate = !negate;
	return *this;
}
