#include <vector>
#include <set>
#include <string>
#include "dig.h"

struct cfg {
	std::vector<std::vector<std::wstring>> g;
	dig<size_t> p, c;
	size_t w, n, len;
	std::set<size_t> *ep, *ec;
	std::set<std::wstring> nulls;
	std::wstring in;
};
