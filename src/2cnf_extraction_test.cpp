#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include "../src/bdd.h"
using namespace std;

// Recursively generate all boolean functions of the given arity

void generate_functions(int arity, unordered_set<spbdd_handle> &func_set, int offset = 0) {
	if(arity == 0) {
		// There are only 2 arity 0 functions
		func_set.insert(hfalse);
		func_set.insert(htrue);
	} else {
		// Build current arity functions with the help of previous arities
		generate_functions(arity - 1, func_set, offset);
		unordered_set<spbdd_handle> pending;
		// Generate the current arity by combining pairs of functions from lower
		// arity depending on whether current variable is 0 or 1
		for(const spbdd_handle &func1 : func_set) {
			for(const spbdd_handle &func2 : func_set) {
				pending.insert((from_bit(offset + arity, true) && func1) || (from_bit(offset + arity, false) && func2));
			}
		}
		// Merge in the newly constructed functions
		func_set.merge(pending);
	}
}

// Test the canonicity of variable shifters
void test_canonicity () {
	bdd::init();
	// First generate set of all boolean functions of given arity
	const int arity = 3;
	unordered_set<spbdd_handle> func_set;
	generate_functions(arity, func_set);
	// Generate single existential quantifications
	vector<bool> base_quant(arity, false);
	vector<vector<bool>> quants;
	for (int i = 0; i < arity; i++) {
		vector<bool> a_quant = base_quant;
		a_quant[i] = true;
		quants.push_back(a_quant);
	}
	cout << "Boolean function count: " << func_set.size() << endl;
	cout << V.size() << endl;
	// Now check that the set is closed under boolean operations
	for (const spbdd_handle &func1: func_set) {
		for (const spbdd_handle &func2: func_set) {
			// Closure under operation means that doing some operation yields a value
			// already in the set

			if (func_set.find(func1 && func2) == func_set.end()) {
				cout << endl
				     << V.size() << endl
				     << "Error: Boolean function set not closed under conjunction."
				     << endl;
				return;
			} else if (func_set.find(func1 || func2) ==
				   func_set.end()) {
				cout << endl
				     << "Error: Boolean function set not closed under disjunction."
				     << endl;
				return;
			} else if (func_set.find(func1 % func2) ==
				   func_set.end()) {
				cout << endl
				     << "Error: Boolean function set not closed under relative complementation."
				     << endl;
				return;
			} //else cout << ".";
		}
		// Check also that existential quantifications are closed
		for (vector<bool> &quant: quants) {
			if (func_set.find(func1 / quant) == func_set.end()) {
				cout << endl
				     << "Error: Boolean function set not closed under existential quantification."
				     << endl;
				return;
			}
		}
	}
	// Control flow passing through here implies set is closed under operations
	cout << endl
	     << "Success: Boolean function set closed under chosen operations."
	     << endl;
	// Now ensure that shifts of the same boolean function have the same BDD
	// First construct the set of BDDs corresponding to the set of functions
}

void test_2cnf_gc () {
	bdd::init();

	poset h;
	h.pure = true;
	poset l;
	l.pure = true;
/*
	poset::insert_eq(h, 1, 1);
	poset::insert_eq(h, 2, 3);
	poset::insert_eq(h, 4, 1);
	poset::insert_eq(h, 5, 2);
	poset::insert_eq(h, 2, 6);
	poset::insert_eq(h, 7, 7);
	poset::insert_eq(h, 8, 8);

	poset::insert_eq(l, 1, 1);
	poset::insert_eq(l, 2, 1);
	poset::insert_eq(l, -3, -2);
	poset::insert_eq(l, 4, 3);
	poset::insert_eq(l, 5, 2);
	poset::insert_eq(l, 6, 6);
	poset::insert_eq(l, 7, 2);
	poset::insert_eq(l, 8, 6);
*/

	poset::insert_var(h, 2);
	poset::insert_var(h,3);

	poset::insert_imp(l, 2, 3);

	poset::print(h, std::cout);
	poset::print(l, cout);

	auto res1 = poset::lift(1, forward<poset>(h), forward<poset>(l));
	poset::print(res1 , std::cout);

	auto high = poset::eval(res1, 1);
	auto low = poset::eval(res1, -1);
	poset::print(high, std::cout);
	poset::print(low, cout);
}

void test_merge_sort () {
	using pu = PersistentUnionFind;

	pu::init(40);

	int puf=0;
	for (int_t i = 2; i<30; ++i) {
		puf = pu::merge(puf, 1, i);
	}

	pu_iterator iter = pu::get_equal(puf, 1);
	pu::MergeSort(iter, iter.end(), puf);

	for (const auto& el : iter) {
		cout << el << endl;
	}
}

int main() {
	//test_2cnf_gc();
	//test_canonicity();
	test_merge_sort();
	return 0;
}