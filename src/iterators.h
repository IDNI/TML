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
#include "input.h"
#include "transform_opt.h"

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
	grey_code_const_iterator& operator++();
	grey_code_const_iterator operator++(int);
	bool operator==(const grey_code_const_iterator rhs) const;
	bool operator!=(const grey_code_const_iterator rhs) const;
	const size_t& operator*() const;

private:
	size_t size_;
	std::vector<size_t> focus_pointers_;
	size_t delta_;

	bool compute_next_delta_();
};

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
class power_set_const_iterator {
public:
	// iterator traits
	using difference_type = size_t;
	using value_type = std::vector<mutation>;
	using pointer = const std::vector<mutation>*;
	using reference = const std::vector<mutation>&;
	using iterator_category = std::input_iterator_tag;

	power_set_const_iterator(std::vector<mutation>& ms);
	power_set_const_iterator();
	power_set_const_iterator& operator++();
	power_set_const_iterator operator++(int);
	bool operator==(power_set_const_iterator rhs) const;
	bool operator!=(power_set_const_iterator rhs) const;
	const std::vector<mutation>& operator*() const;
private:
	grey_code_const_iterator grey_code;
	std::vector<mutation> set;
	std::vector<mutation> subset;
};

class powerset_range {
public:

	powerset_range(std::vector<mutation>& ms);
	bool empty();
	power_set_const_iterator begin();
	power_set_const_iterator end();
private:
	std::vector<mutation> set;
};

/*!
 * Iterator returning all the subsets of a given set. It uses the 
 * grey_code_const_iterator under the hood.
 */
class powerset_iterator {	
public:
	// iterator traits
	using difference_type = size_t;
	using value_type = std::vector<raw_prog*>;
	using pointer = const std::vector<raw_prog*>*;
	using reference = const std::vector<raw_prog*>&;
	using iterator_category = std::input_iterator_tag;

	// constructor
	powerset_iterator(std::vector<raw_prog*>& s) : set{s} {}
	powerset_iterator() {}

	// end
	static powerset_iterator& end();	// iterator methods
	powerset_iterator& operator++();
	powerset_iterator operator++(int);
	bool operator==(powerset_iterator that) const;
	bool operator!=(powerset_iterator that) const;
	std::vector<raw_prog*> operator*();
private:
	std::vector<raw_prog*> set;
	std::vector<raw_prog*> subset;

	bool next();
};

#endif // __ITERATORS_H__
