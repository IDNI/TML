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

int main() {
  bdd::init();
  // First generate set of all boolean functions of given arity
  const int arity = 3;
  unordered_set<spbdd_handle> func_set;
  generate_functions(arity, func_set);
  // Generate single existential quantifications
  vector<bool> base_quant(arity, false);
  vector<vector<bool>> quants;
  for(int i = 0; i < arity; i++) {
    vector<bool> a_quant = base_quant;
    a_quant[i] = true;
    quants.push_back(a_quant);
  }
  cout << "Boolean function count: " << func_set.size() << endl;
  // Now check that the set is closed under boolean operations
  for(const spbdd_handle &func1 : func_set) {
    for(const spbdd_handle &func2 : func_set) {
      // Closure under operation means that doing some operation yields a value
      // already in the set
      if(func_set.find(func1 && func2) == func_set.end()) {
        cout << endl << "Error: Boolean function set not closed under conjunction." << endl;
        return 1;
      } else if(func_set.find(func1 || func2) == func_set.end()) {
        cout << endl << "Error: Boolean function set not closed under disjunction." << endl;
        return 1;
      } else if(func_set.find(func1 % func2) == func_set.end()) {
        cout << endl << "Error: Boolean function set not closed under relative complementation." << endl;
        return 1;
      } else cout << ".";
      // Check closure under ternary operations
      for(const spbdd_handle &func3 : func_set) {
        if(func_set.find(bdd_ite(func1, func2, func3)) == func_set.end()) {
          cout << endl << "Error: Boolean function set not closed under conditioned disjunction." << endl;
          return 1;
        }
      }
    }
    // Check also that existential quantifications are closed
    for(vector<bool> &quant : quants) {
      if(func_set.find(func1 / quant) == func_set.end()) {
        cout << endl << "Error: Boolean function set not closed under existential quantification." << endl;
        return 1;
      }
    }
  }
  // Control flow passing through here implies set is closed under operations
  cout << endl << "Success: Boolean function set closed under chosen operations." << endl;
  // Now ensure that shifts of the same boolean function have the same BDD
  // First construct the set of BDDs corresponding to the set of functions
  unordered_set<bdd_ref> func_bdd_set;
  for(const spbdd_handle &func : func_set) {
    func_bdd_set.insert(GET_BDD_ID(func->b));
  }
  // Now check that the set of boolean functions higher variables are still
  // represented using the same BDD
  for(int shift = 1; shift < 10; shift++) {
    // Generate the set of boolean functions over higher variables
    unordered_set<spbdd_handle> func_set2;
    generate_functions(arity, func_set2, shift);
    // Now extract the BDDs of this set of higher boolean functions
    unordered_set<bdd_ref> func_bdd_set2;
    for(const spbdd_handle &func : func_set2) {
      func_bdd_set2.insert(GET_BDD_ID(func->b));
    }
    // Now ensure that the BDD sets are identical and that the functions are not
    if(func_set == func_set2) {
      cout << endl << "Error: Shifted function set cannot be identical to the original." << endl;
      return 2;
    } else if(func_bdd_set != func_bdd_set2) {
      cout << endl << "Error: Shifted function set should have BDDs identical to the original's." << endl;
      return 3;
    }
  }
  // Control flow passing through here implies shifts share BDDs
  cout << endl << "Success: Boolean function set is represented by same BDDs despite variable shifts." << endl;
  // Now we want to make sure that every BDD combined with an input inverter and
  // variable shifter represents exactly two functions and that these two
  // functions are output inverses of each other.
  map<tuple<int, int, bool>, vector<bool>> func_out_inv_split;
  // Represent the output inversion attribute separately from other attributes
  for(const spbdd_handle &func : func_set) {
    func_out_inv_split[make_tuple((int) GET_BDD_ID(func->b), (int) GET_SHIFT(func->b), (bool) GET_INV_INP(func->b))].push_back(GET_INV_OUT(func->b));
  }
  if(2 * func_out_inv_split.size() != func_set.size()) {
    // Ensure that the function set modulo output inversion is exactly half the original's size
    cout << endl << "Error: Output inversion attribute does not equipartition function set into two sets." << endl;
    return 4;
  } else {
    // Ensure that each function BDD has its output inverted version in the function set
    for(const auto &[func_part, inv_outs] : func_out_inv_split) {
      if(inv_outs.size() < 2) {
        cout << endl << "Error: At least one function-inverse pair is not represented with the same BDD." << endl;
        return 5;
      } else if(inv_outs.size() > 2) {
        cout << endl << "Error: At least one function is over-represented in the function set." << endl;
        return 5;
      } else if (inv_outs[0] == inv_outs[1]) {
        cout << endl << "Error 1: At least one function-inverse pair is not represented with the same BDD." << endl;
        cout << endl << "Error 2: At least one function is over-represented in the function set." << endl;
        return 5;
      }
    }
  }
  // Control flow passing through here implies that output inversion equipartitions function set
  cout << endl << "Success: Boolean function set is equipartitioned into two sets by the output inversion attribute." << endl;
  return 0;
}
