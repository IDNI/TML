#include "bdd.h"

class bdd_eq_ex {
	const size_t bits, nvars;
	const std::vector<size_t>& e;
	const std::set<size_t> s;
	std::vector<short> path;
	size_t compute(size_t x, size_t v);
	std::set<size_t> get_s() const;
public:
	bdd_eq_ex(size_t x, size_t bits, size_t ar, const std::vector<size_t>&e);
	size_t res;
};
