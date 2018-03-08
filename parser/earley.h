#include <vector>
#include <set>
#include "dig.h"

struct cfg* cfg_create(const std::vector<std::vector<const wchar_t*>>&, const wchar_t* S);
void cfg_parse(struct cfg*, const wchar_t*);
struct cfg* cfg_create(const std::vector<std::vector<std::wstring>>&, const wchar_t* S);
void cfg_delete(struct cfg*);
