#include <vector>
#include <set>
#include <string>
#include "dig.h"

struct cfg {
	std::vector<std::vector<std::wstring>> g;
	dig<size_t> p, c;//, ep, ec;
	size_t w, n, len;
	std::set<size_t> *ep, *ec;
	std::map<size_t, std::set<size_t>> done;
	std::wstring in;
};
// max(ei) = len * max(dr) = len * w * g.size()
// tc optimization for len*ei = es:
// can have an edge only to larger items (poswise)
// (setwise)
cfg* cfg_create(std::vector<std::vector<std::wstring>>, const std::wstring& S);
void cfg_parse(cfg&, const std::wstring&);
