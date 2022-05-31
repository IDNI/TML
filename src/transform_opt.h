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

#include "driver.h"

/*!
 * Represents a mutation of a given (mutated) program. If selected, it is
 * applied to the given (mutated) program. This is a cheap implementation of
 * the command pattern.
 */
typedef std::function<bool(class mutated_prog&)> mutation;

/*!
 * Represents a mutated program, i.e. the original program, the additions and 
 * substractions.
 */
struct mutated_prog  {
	// empty
	mutated_prog();
	// starting node of the mutated progs log
	mutated_prog(raw_prog *p);
	// link to previous mutated prog
	mutated_prog(mutated_prog *m);

	// link to previous mutated prog
	mutated_prog(const mutated_prog &m);

	void operator()(mutation& m);
	mutated_prog* operator--();
	std::vector<raw_rule> get_rules();
	raw_prog to_raw_program();

	raw_prog* current;
	std::vector<raw_rule*> deletions;
	mutated_prog* previous;
};

/*!
 * Computes the approximate cost of executing a given mutated program.
 */
using cost_function = std::function<float(mutated_prog&)>;

/*!
 * Computes the approximate cost of executing a given mutated program.
 */
using brancher = std::function<std::vector<mutation>(mutated_prog&)>;


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
	best_solution(cost_function& f);
	virtual bool bound(mutated_prog& p);
	virtual raw_prog solution();
private:
	cost_function cost;
	std::map<float, mutated_prog> bests; 
};

/*!
 * Optimization plan accordignly to command line options
 */
struct optimization_plan {
	std::vector<brancher> begin;
	std::vector<brancher> loop;
	std::vector<brancher> end;

	bounder& bounder;
}
#endif // __TRANSFORM_OPT_H__