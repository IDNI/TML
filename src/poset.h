#ifndef TML_POSET_H
#define TML_POSET_H

#include <unordered_map>
#include <vector>
#include <memory>
#include <functional>
#include "defs.h"
#include "persistent_dag.h"
#include "persistent_union_find.h"
#include "persistent_set.h"

class poset;

// The vector represents the canonical 2-CNF universe
extern std::vector<poset> P;
extern std::unordered_map<poset, int_t> MP;

template<>
struct std::hash<poset> {
	size_t operator()(const poset &) const;
};

template<>
struct std::hash<std::pair<int_t, std::pair<int_t, int_t>>> {
	size_t
	operator()(const std::pair<int_t, std::pair<int_t, int_t>> &) const;
};

/*
 * A poset contains the 2-CNF part of a BDD.
 * The storage is divided into three persistent data structures.
 * UnionFind for the equal variables, DAG for the implications and Sets for
 * single variables being True or False.
 */
class poset {
	using pu = persistent_union_find;
	using pd = persistent_dag;
	using ps = persistent_set;
	using imap = std::unordered_map<int_t,int_t>;
	using pvector = std::vector<std::pair<int_t,int_t>>;
	// Equal variables, represented by a pointer to the uf_univ
	int_t eqs = 0;
	// Implications, represented by a pointer to the dag_univ
	int_t imps = 0;
	// Singletons, represented by a pointer to the set_univ
	int_t vars = 0;

	// Indicates the set of variables in the poset
	int_t v = 0;

	// These functions are used during the extraction process of the 2-CNF
	// that emerges from a high and a low node
	static void lift_imps(poset &p, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo);
	static void lift_vars(poset &p, int_t v, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo, pvector& eq_lift);
	static void lift_eqs(poset &p, int_t v, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo, pvector& eq_lift);

	// This eq insertion does not introduce new variables
	static void insert_eq(poset &p, std::vector<int_t>& eq);
	// Insert a variable without checking if implications are affected
	static void insert_var_no_imp(poset &p, int_t v);
	// Insert and remove from the set representing which
	// variables are present in the 2-CNF
	void insert_v(int_t vv) { v = ps::insert(v, abs(vv)); }
	void rm_v(int_t vv) { v = ps::remove(v, abs(vv)); }
  public:
	// Indicates if the poset has an associated BDD part
	bool pure = false;

	poset() = default;

	//Creates single variable poset
	explicit poset(int_t v) : pure(true) { insert_var(*this, v); }

	explicit poset(bool isPure) : pure(isPure) {}

	friend std::hash<poset>;
	bool operator==(const poset &p) const;

	static void init(int n) {
		P.emplace_back(false);
		MP.emplace(false, 0);
		P.emplace_back(true);
		MP.emplace(true, 1);
		pd::init(n);
	};

	int_t get_v() const { return ps::get(v).e; }

	static bool resize(int n) {
		return pu::resize(n);
	};

	static int_t size() {
		// The only data structure that needs size control is union find
		return pu::size();
	};

	// Canonically add a poset to the universe P
	static int_t add_P (poset& p) {
		if(auto iter = MP.find(p); iter != MP.end())
			return iter->second;
		P.push_back(p);
		MP.emplace(p, P.size()-1);
		return (int_t) P.size()-1;
	}

	// Conjunct two posets
	static poset conjunct(const poset& x, const poset& y);
	// Extract the poset belonging to (v,h,l) from the posets of h and l
	static poset lift(int_t v, int_t h, int_t l);
	// Evaluate the poset p on v
	static poset eval(const poset &p, int_t v);
	// Negate the poset if it is negatable
	static poset negate(const poset &p);
	// Check if negation of poset is still a poset
	static bool negatable(poset &p);
	// Insert a variable to poset and apply all reductions to stay canonical
	static void insert_var(poset &p, int_t v);
	static poset insert_var(poset &&p, int_t v);
	// Insert an implication and apply all reductions to stay canonical
	static void insert_imp(poset &p, std::pair<int_t, int_t> &el);
	static void insert_imp(poset &p, int_t fst, int_t snd);
	// Insert an equality and apply all reductions to stay canonical
	static void insert_eq(poset &p, int_t v1, int_t v2);
	// Get a poset from the universe at position pos
	static poset get(int_t pos);
	static void print(poset &p, std::ostream &os);
	static void print(poset &&p, std::ostream &os);

	inline static bool is_empty(const poset &p) {
		return p.eqs + p.imps + p.vars == 0;
	}

	inline static bool only_vars(const poset &&p) {
		return p.eqs + p.imps == 0 && p.vars > 0;
	}
};

#endif  // TML_POSET_H