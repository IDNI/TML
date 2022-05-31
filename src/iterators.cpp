// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.

#include <numeric>
#include <ranges>

#include "input.h"
#include "transform_opt.h"
#include "iterators.h"

using namespace std;

bool grey_code_const_iterator::compute_next_delta_() {
	if (focus_pointers_[0] == size_) return false;
	delta_ = focus_pointers_[0];
	focus_pointers_[delta_] = focus_pointers_[delta_ + 1];
	focus_pointers_[delta_ + 1] = delta_ + 1;
	return true;
}

grey_code_const_iterator::grey_code_const_iterator(size_t size): size_(size) {
	focus_pointers_.resize(size_++);
	std::iota(focus_pointers_.begin(), focus_pointers_.end(), 0);
	delta_ = 0;
}

grey_code_const_iterator::grey_code_const_iterator(): size_(0), delta_(0) {
	focus_pointers_[0] = 0;
}

grey_code_const_iterator& grey_code_const_iterator::operator++() {
	if (compute_next_delta_()) return *this;
	grey_code_const_iterator end;
	return end;
}

grey_code_const_iterator grey_code_const_iterator::operator++(int) {
	grey_code_const_iterator previous(*this);
	if (!compute_next_delta_()) {
		size = 0;
	}
	return previous;
}

bool grey_code_const_iterator::operator==(const grey_code_const_iterator rhs) const {
	// checking equality from cheapest to most expensive
	return size_ == rhs.size_ && delta_ == rhs.delta_ && focus_pointers_ == rhs.focus_pointers_;
}

bool grey_code_const_iterator::operator!=(const grey_code_const_iterator rhs) const {
	return !(*this == rhs);
}

const size_t& grey_code_const_iterator::operator*() const {
	return delta_;
}

grey_code_range::grey_code_range(size_t s) : size(s) {}

bool grey_code_range::empty() {
	return size == 0;
}

grey_code_const_iterator grey_code_range::begin() {
	grey_code_const_iterator begin(size);
	return begin;
}

grey_code_const_iterator grey_code_range::end() {
	grey_code_const_iterator end;
	return end;
}

/*!
 * Iterator returning all the subsets of a given set. It uses the 
 * grey_code_const_iterator under the hood.
 */
power_set_const_iterator::power_set_const_iterator(vector<mutation>& s) : set{s} {
	grey_code_const_iterator gc(s.size());
	grey_code = gc;
}

power_set_const_iterator::power_set_const_iterator() {}

power_set_const_iterator& power_set_const_iterator::operator++() {
	auto delta = *(grey_code++);
	auto it = find(subset.begin(), subset.end(), set[delta]);
	if (it != subset.end())
		subset.erase(it);
	else 
		subset.push_back(set[delta]);
	return *this;
}
	
power_set_const_iterator power_set_const_iterator::operator++(int) {
	auto current = *this; 
	auto delta = *(grey_code++);
	auto it = find(subset.begin(), subset.end(), set[delta]);
	if (it != subset.end())
		subset.erase(it);
	else 
		subset.push_back(set[delta]);
	return current;
}
	
bool power_set_const_iterator::operator==(power_set_const_iterator that) const {
	return set == that.set && subset == that.subset;
}
	
bool power_set_const_iterator::operator!=(power_set_const_iterator that) const {
	return !(*this == that);
}

const vector<mutation>& power_set_const_iterator::operator*() const {
	return subset;
}

powerset_range::powerset_range(vector<mutation>& ms) : set(ms) {}

bool powerset_range::empty() {
	return set.size() == 0;
}

power_set_const_iterator powerset_range::begin() {
	power_set_const_iterator begin(set);
	return begin;
}

power_set_const_iterator powerset_range::end() {
	power_set_const_iterator end;
	return end;
}
