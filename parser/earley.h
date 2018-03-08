#include <vector>
#include <set>
#include "dig.h"

struct cfg {
	std::vector<std::vector<const wchar_t*>> g;
	dig<size_t> p, c;//, ep, ec;
	size_t w, n, len;
	std::set<size_t> *ep, *ec;
	std::map<size_t, std::set<size_t>> done;
	const wchar_t *in;
};
// max(ei) = len * max(dr) = len * w * g.size()
// tc optimization for len*ei = es:
// can have an edge only to larger items (poswise)
// (setwise)
cfg* cfg_create(const std::vector<std::vector<const wchar_t*>>&, const wchar_t* S);
void cfg_parse(cfg*, const wchar_t*);
// for convenience:
cfg* cfg_create(const std::vector<std::vector<std::wstring>>&, const wchar_t* S);
