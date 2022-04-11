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
	const int arity = 5;
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
	spbdd_handle a = from_bit(2, true);
	spbdd_handle b  = a && from_bit(3, true);
	bdd::stats(cout);
	cout << endl;
	bdd::gc();
	bdd::stats(cout);
	return;
}

int main() {
	test_2cnf_gc();
	//test_canonicity();
	return 0;
}