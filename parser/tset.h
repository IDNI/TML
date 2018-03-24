#include <vector>
#include <set>
#include <cstring>
#include <array>
#include <iostream>
#include <cassert>
#include <map>
using namespace std;

typedef int32_t int_t;
typedef int_t* vec;
typedef const int_t* vecc;
typedef map<int_t, int_t> env;
const size_t max_arity = 256;

class tset { // tuple set
	struct cmp {
		const size_t k, a;
		cmp(size_t k, size_t a) : k(k), a(a) {}
		bool operator()(vecc x, vecc y) const;
	};
public:
	typedef set<vecc>::const_iterator set_iter;
	typedef pair<size_t, array<set_iter, 2>> iter_pair;
	typedef vector<iter_pair> iters;
	typedef vector<array<size_t, 2>> eqs;

	tset(size_t arity);
	void add(vecc);
	vecc first(vecc, iters&) const;
	vecc next(vecc, iters&) const;
private:
	size_t arity;
	set<vecc, cmp> **s;
	int icmp(vecc x, vecc y) const;
	set_iter first(size_t n, int_t i) const;
};
