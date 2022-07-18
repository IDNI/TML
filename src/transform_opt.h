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

#ifndef __TRANSFORM_OPT_H__
#define __TRANSFORM_OPT_H__

#include <vector>
#include <map>
#include <cmath>
#include <functional>
#include <limits>

class raw_prog;
class dict_t;

/*!
 * Represents a mutated program, i.e. the original program, the additions and 
 * substractions.
 */
struct mutated_prog  {
	// starting node of the mutated progs log
	mutated_prog(raw_prog &rp): 
	//		original(rp), 
			current(rp), 
			previous(nullptr) {};
	// link to previous mutated prog
	mutated_prog(mutated_prog *mp): 
	//		original(mp->original), 
			previous(mp), 
			current(mp->current) {};

	void operator()(struct mutation& m);

	raw_prog current;
	mutated_prog *previous;
};

/*!
 * Represents a mutation of a given (mutated) program. If selected, it is
 * applied to the given (mutated) program. This is a cheap implementation of
 * the command pattern.
 */
class mutation {
public:
	auto operator<=>(const mutation &rhs) const = default;
	virtual bool const operator()(mutated_prog &mp) const = 0;
};

/*!
 * Computes the approximate cost of executing a given mutated program.
 */
using cost_function = std::function<size_t(mutated_prog&)>;
extern cost_function exp_in_heads;

/*!
 * Computes the approximate cost of executing a given mutated program.
 */
using brancher = std::function<std::vector<std::shared_ptr<mutation>>(mutated_prog&)>;

/**
 * Represents and strategy to select the best mutation according to the passed
 * cost_function.
 */
class bounder {
public:
	virtual bool bound(mutated_prog& p) = 0;
	virtual raw_prog solution() = 0;
};

/*!
 * Custom implementation of bounder interface that returns the best solution found
 * so far.
 */
class best_solution: public bounder {
public:
	best_solution(cost_function& f, mutated_prog &rp): 
			func_(f), 
			cost_(std::numeric_limits<size_t>::max()) {
		best_[f(rp)] = std::make_shared<mutated_prog>(rp);
	};
	virtual bool bound(mutated_prog& p);
	virtual raw_prog solution();
private:
	cost_function func_;
	size_t cost_;
	std::map<size_t, std::shared_ptr<mutated_prog>> best_;
//	raw_prog best_; 
//	std::reference_wrapper<mutated_prog> best_; 
};

/*!
 * Optimization plan accordignly to command line options
 */
struct optimization_plan {
public:
	std::vector<brancher> begin;
	std::vector<brancher> loop;
	std::vector<brancher> end;
	bounder& bndr;

	optimization_plan(bounder &b);
};

raw_prog optimize(raw_prog &program, optimization_plan &plan);

#endif // __TRANSFORM_OPT_H__