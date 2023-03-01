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

extern std::vector<poset> P, NP;
extern std::unordered_map<poset, int_t> MP, MNP;

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

	static void lift_imps(poset &p, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo);
	static void lift_vars(poset &p, int_t v, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo, pvector& eq_lift);
	static void lift_eqs(poset &p, int_t v, poset &hi, poset &lo, imap &eq_lift_hi, imap &eq_lift_lo, pvector& eq_lift);

	static void insert_eq(poset &p, std::vector<int_t>& eq);
  public:
	// Indicates if the poset has an associated BDD part
	bool pure = false;
	// Indicates the smallest variable in the poset
	int_t v = 0;

	poset() = default;

	//Creates single variable poset
	explicit poset(int_t v) : pure(true), v(abs(v)) { insert_var(*this, v); }

	explicit poset(bool isPure) : pure(isPure) {}

	friend std::hash<poset>;
	bool operator==(const poset &p) const;

	static void init(int n) {
		P.emplace_back(true);
		P.emplace_back(true);
		NP.emplace_back(true);
		NP.emplace_back(false);
		pd::init();
	};

	static bool resize(int n) {
		return pu::resize(n);
	};

	static int_t size() {
		// The only data structure that needs size control is union find
		return pu::size();
	};

	static poset conjunct(const poset& x, const poset& y);
	static poset lift(int_t v, int_t h, int_t l);
	static poset eval(const poset &p, int_t v);
	static poset negate(const poset &p);
	static bool negatable(poset &p);
	//TODO: insert_var needs to update imps and eqs
	static bool insert_var(poset &p, int_t v);
	static poset insert_var(poset &&p, int_t v);
	//TODO: insert_imp needs to check present vars before insertion and containment in equalities
	static void insert_imp(poset &p, std::pair<int_t, int_t> &el);
	static void insert_imp(poset &p, int_t fst, int_t snd);
	//TODO: insert_eq needs to check vars and imps
	static void insert_eq(poset &p, int_t v1, int_t v2);
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