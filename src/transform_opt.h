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

#include "ir_builder.h"

class raw_prog;
class dict_t;

/* Optimization methods. */

/*! Square a datalog falt program. */
flat_prog square_program(const flat_prog &fp);

/* Optimization branch and bound definitions. */

/*! Represents a mutated program, i.e. the original program, the additions and 
 * substractions. */
struct changed_prog  {
	// starting node of the mutated progs log
	explicit changed_prog(flat_prog &rp): current(rp) {};
	// link to previous mutated prog
	explicit changed_prog(changed_prog *mp): current(mp->current) {};
	void operator()(struct change& m);

	flat_prog current;
};

/*! Represents a change of a given (mutated) program. If selected, it is
 * applied to the given (mutated) program. This is a cheap implementation of
 * the command pattern. */
class change {
public:
	flat_prog clashing;

	explicit change() = default;
	explicit change(flat_prog &c): clashing(c) {}
	explicit change(std::vector<term> &r) { clashing.insert(r); }
	virtual ~change() = default;

	auto operator<=>(const change &rhs) const = default;
	virtual bool operator()(changed_prog &mp) const = 0;
};

/*! Computes the approximate cost of executing a given mutated program. */
using cost_function = std::function<size_t(changed_prog&)>;
extern const cost_function exp_in_heads;

/*! Computes the approximate cost of executing a given mutated program. */
using brancher = std::function<std::vector<std::shared_ptr<change>>(changed_prog&)>;

/*! Represents and strategy to select the best change according to the passed
 * cost_function. */
class bounder {
public:
	virtual bool bound(changed_prog& p) = 0;
	virtual flat_prog solution() = 0;
};

/*! Custom implementation of bounder interface that returns the best solution found
 * so far. */
class best_solution: public bounder {
public:
	best_solution(cost_function& f, changed_prog &rp): 
			func_(f), 
			cost_(std::numeric_limits<size_t>::max()), 
			best_(std::make_shared<changed_prog>(rp)) {};

	virtual bool bound(changed_prog& p);
	virtual flat_prog solution();
private:
	cost_function func_;
	size_t cost_;
	std::shared_ptr<changed_prog> best_;
};

/*! Optimization plan accordignly to command line options. */
struct plan {
public:
	std::vector<brancher> branchers;
	std::reference_wrapper<bounder> bndr;

	plan(bounder &b): bndr(b) {};
};

// raw_prog optimize_once(flat_prog &program, plan &plan);
// raw_prog optimize_loop(flat_prog &program, plan &plan);

#endif // __TRANSFORM_OPT_H__