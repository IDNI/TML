#include "bdd.h"

class query {
	const size_t bits, nvars;
	const std::vector<int_t>& e;
	const int_t glt, ggt;
	const std::vector<int_t> excl;
	const std::set<size_t> s;
	std::vector<char> path;
	size_t compute(size_t x, size_t v);
	std::set<size_t> get_s() const;
public:
	query(size_t x, size_t bits, size_t ar, const std::vector<int_t>& e,
		int_t glt=0, int_t ggt=0, const std::vector<int_t>& excl={});
	size_t res;
};
