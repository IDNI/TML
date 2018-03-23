#include <vector>
#include <set>
#include <cstring>
#include <array>
#include <iostream>
#include <cassert>
using namespace std;
#define ever ;;

class tset { // tuple set
	size_t arity;
	struct cmp {
		const size_t k, a;
		cmp(size_t k, size_t a) : k(k), a(a) {}
		bool operator()(const int32_t* x, const int32_t* y) {
			return x[k] == y[k] ? memcmp(x, y, a*sizeof(const int32_t*)) < 0 : x[k] < y[k];
		}
	};
	set<const int32_t*, cmp> **s;
	int32_t* buf;
	set<const int32_t*>::const_iterator first(size_t n, int32_t i) {
		buf[n] = i;
		auto it = s[n]->lower_bound(buf);
		return buf[n] = 0, it;
	}
	set<const int32_t*>::const_iterator last(size_t n, int32_t i) {
		buf[n] = i+1;
		auto it = s[n]->upper_bound(buf);
		return buf[n] = 0, it;
	}
public:
	typedef vector<array<set<const int32_t*>::const_iterator, 2>> iters;

	tset(size_t arity) : arity(arity), s(new set<const int32_t*, cmp>*[arity]), buf(new int32_t[arity]) {
		for (size_t n = 0; n < arity; ++n) s[n] = new set<const int32_t*, cmp>(cmp(n, arity));
		memset(buf, 0, sizeof(const int32_t*) * arity);
	}

	void add(const int32_t* t) { for (size_t n = 0; n < arity; ++n) s[n]->emplace(t); }

	bool first(const int32_t* pat, iters& it) {
		for (size_t n = 0; n < arity; ++n)
			if (pat[n] > 0) {
				if (auto lb = first(n, pat[n]); lb != s[n]->end())
					it.emplace_back(array<set<const int32_t*>::const_iterator, 2>{lb, last(n, pat[n])});
				else return false;
			}
		return true;
	}

	const int32_t* next(iters& it) {
		for(ever) {
			if (it[0][0] == it[0][1]) return 0;
			for (size_t n = 1; n < it.size(); ++n) {
				if (it[n][0] == it[n][1]) return 0;
				while (memcmp(*it[n][0], *it[n-1][0], sizeof(const int32_t*) * arity) < 0)
					if (++it[n][0] == it[n][1])
						return 0;
				while (memcmp(*it[n][0], *it[n-1][0], sizeof(const int32_t*) * arity) > 0)
					if (++it[n-1][0] == it[n-1][1])
						return 0;
			}
			return *(it[0][0]++);
		}
	}
};

int main(int, char**) {
	tset s(3);
	int32_t a[]={1,2,3};
	int32_t b[]={2,3,4};
	int32_t c[]={1,2,4};
	int32_t d[]={1,1,3};
	int32_t e[]={4,3,4};
	int32_t q[]={-1,3,4};
	const int32_t *r;
	s.add(a), s.add(b), s.add(c), s.add(d), s.add(e);
	tset::iters it;
	assert(s.first(q, it));
	while ((r = s.next(it))) {
		for (size_t n = 0; n < 3; ++n)
			cout << r[n] << ' ';
		cout << endl;
	}
}
