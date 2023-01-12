#include "persistent_set.h"

using namespace std;

using ps = persistent_set;

static std::vector<ps> set_univ;
static std::unordered_map<ps, int_t> set_memo;

namespace { abs_cmp_ abs_cmp; }

size_t std::hash<ps>::operator()(const ps &s) const {
	return hash_pair(s.e, s.n);
}

bool ps::operator==(const ps &s) const {
	return e == s.e && n == s.n;
}

int_t ps::add(int_t e, int_t n) {
	ps set = ps(e, n);
	if (auto it = set_memo.find(set); it != set_memo.end())
		return it->second;
	else
		return set_memo.emplace(set, set_univ.size()),
			set_univ.emplace_back(set), (int_t) set_univ.size() - 1;
}

bool ps::empty(int_t set_id) {
	return set_id == 0;
}

void ps::init() {
	set_univ.emplace_back(ps(0, 0));
	set_memo.emplace(ps(0, 0), 0);
}

int_t ps::next(int_t set_id) {
	return set_univ[set_id].n;
}

bool ps::contains(int_t set_id, int_t elem) {
	while (set_id != 0) {
		if (set_univ[set_id].e == elem) return true;
		set_id = next(set_id);
	}
	return false;
}

int_t ps::insert(int_t set_id, int_t elem) {
	int_t el = set_univ[set_id].e;
	if (el == elem) return set_id;

	int_t r;
	if (abs_cmp(elem, el) || el == 0) r = add(elem, set_id);
	else r = add(el, insert(set_univ[set_id].n, elem));

	return r;
}

int_t ps::remove(int_t set_id, int_t elem) {
	int_t el = set_univ[set_id].e;
	if (el == elem) return set_univ[set_id].n;
		// In this case the element does not belong to the set
	else if (abs_cmp(elem, el) || el == 0) return set_id;
	else return add(el, remove(set_univ[set_id].n, elem));
}

ps ps::get(int_t set_id) {
	return set_univ[set_id];
}

void ps::print(int_t set_id, ostream &os) {
	os << "{";
	while (set_id != 0) {
		os << set_univ[set_id].e;
		set_id = next(set_id);
		if (set_id != 0) os << ", ";
	}
	os << "}" << std::endl << std::endl;
}

int_t ps::find(int_t set_id, int_t elem) {
	while (set_id != 0) {
		if (set_univ[set_id].e == elem) return set_id;
		set_id = next(set_id);
	}
	return 0;
}