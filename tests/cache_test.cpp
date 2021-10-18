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
  bdd::init(MMAP_NONE, 10000, "", true, -1U);
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
  size_t orig_ite_cache_size = bdd::ite_cache_size();
  cout << endl << "Info: Cache size before conducting shifted computations is " << orig_ite_cache_size << "." << endl;
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
  const size_t ite_cache_size = bdd::ite_cache_size();
  if(ite_cache_size <= orig_ite_cache_size) {
    cout << endl << "Error: Unshifted BDD computations caused the cache to shrink by " << (orig_ite_cache_size - ite_cache_size) << "." << endl;
    return 4;
  } else {
    cout << endl << "Info: Unshifted BDD computations caused the cache to grow by " << (ite_cache_size - orig_ite_cache_size) << "." << endl;
  }
  // Now check that the set of boolean functions higher variables are still
  // represented using the same BDD
  for(int shift = 1; shift < 10; shift++) {
    unordered_set<spbdd_handle> func_set2;
    // Now check that the set is closed under boolean operations
    for(const spbdd_handle &func1 : func_set) {
      for(const spbdd_handle &func2 : func_set) {
        // Do BDD operations on shifted elements with intent to study changes to
        // the cache afterwards
        func_set2.insert(bdd_shift(func1, shift) && bdd_shift(func2, shift));
        func_set2.insert(bdd_shift(func1, shift) || bdd_shift(func2, shift));
        func_set2.insert(bdd_shift(func1, shift) % bdd_shift(func2, shift));
        for(const spbdd_handle &func3 : func_set) {
          func_set2.insert(bdd_ite(bdd_shift(func1, shift), bdd_shift(func2, shift), bdd_shift(func3, shift)));
        }
      }
    }
    if(func_set.size() != func_set2.size()) {
      cout << endl << "Error: Boolean function set generated by set shifted by " << shift << " not equinumerous to that generated by original set." << endl;
      return 2;
    } else if(bdd::ite_cache_size() != ite_cache_size) {
      cout << endl << "Error: Cache not being used to short-circuit BDD computations shifted by " << shift << "." << endl;
      return 3;
    } else {
      // Control flow passing through here implies that BDD computations are most-likely short-circuited
      cout << endl << "Success: BDD computations shifted by " << shift << " were most-likely short-circuited using the cache." << endl;
    }
  }
  return 0;
}
