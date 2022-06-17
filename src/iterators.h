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

#ifndef __ITERATORS_H__
#define __ITERATORS_H__

#include <vector>
#include <set>
#include <ranges>


/*!
* Iterator returning the deltas needed to generate grey codes of a certain
* size following Algorithm L (Loopless Gray binary generation) from Knuth 
* Vol 4A (originally published by Bitner, Ehrlich and Reingold, CACM 19 (1976), 
* pp. 517-521). 
*/
class grey_code_const_iterator {
public:
	// iterator traits
	using difference_type = size_t;
	using value_type = size_t;
	using pointer = const size_t*;
	using reference = const size_t&;
	using iterator_category = std::input_iterator_tag;

	grey_code_const_iterator(size_t size);
	grey_code_const_iterator();
	grey_code_const_iterator &operator++();
	grey_code_const_iterator operator++(int);
	bool operator==(const grey_code_const_iterator rhs) const;
	bool operator!=(const grey_code_const_iterator rhs) const;
	const size_t &operator*() const;

private:
	std::vector<size_t> focus_pointers_;
	size_t size_;
	size_t delta_;

	bool compute_next_delta_();
};

/*!
 * Range returning iterators to Grey Codes up to a given integer.
 */
class grey_code_range {
public:

	grey_code_range(size_t size);
	bool empty();
	grey_code_const_iterator begin();
	grey_code_const_iterator end();

private:
	size_t size;
};

/*!
 * Iterator returning all the subsets of a given set. It uses the 
 * grey_code_const_iterator under the hood.
 */
template<class T>
class power_set_const_iterator {
public:
	// iterator traits
	using difference_type = size_t;
	using value_type = std::vector<T>;
	using pointer = const std::vector<T>;
	using reference = const std::vector<T>&;
	using iterator_category = std::input_iterator_tag;

	power_set_const_iterator(std::vector<T>& s) : set{s} {
		grey_code_const_iterator gc(s.size());
		grey_code = gc;
	}

	power_set_const_iterator() {}

	power_set_const_iterator &operator++() {
		auto delta = *(++grey_code);
		auto it = subset.find(delta);
		if (it != subset.end())
			subset.erase(it);
		else 
			subset.insert(delta);
		return *this;
	}

	power_set_const_iterator operator++(int) {
		auto current = *this; 
		auto delta = *(++grey_code);
		auto it = subset.find(delta);
		if (it != subset.end())
			subset.erase(it);
		else 
			subset.insert(delta);
		return current;
	}

	bool operator==(power_set_const_iterator &that) const {
		return set == that.set && subset == that.subset;
	}

	bool operator!=(power_set_const_iterator &that) const {
		return !(*this == that);
	}		

	const std::vector<T> operator*() const{
		auto mutations = subset | std::views::transform([this](size_t idx ) { return set[idx]; });
		std::vector<T> v(mutations.begin(), mutations.end());
		return v;
	}

private:
	grey_code_const_iterator grey_code;
	std::vector<T> set;
	std::set<size_t> subset;
};

/*!
 * Range returning iterators to the poserset of the provided set.
 */
template<class T>
class powerset_range {
public:

	powerset_range(std::vector<T>& ms) : set(ms) {}
	
	bool empty() {
		return set.size() == 0;
	}

	power_set_const_iterator<T> begin() {
		power_set_const_iterator<T> begin(set);
		return begin;
	}

	power_set_const_iterator<T> end() {
		power_set_const_iterator<T> end;
		return end;
	}

private:
	std::vector<T> set;
};

#endif // __ITERATORS_H__
