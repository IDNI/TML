#include <string>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <functional>
#include <algorithm>
#include <iostream>
#include "earley.h"
using namespace std;

#define _DEBUG
#ifdef _DEBUG
#define DEBUG(x) x
typedef const wchar_t* wsptr;
wsptr dbg[10];
void db(size_t n, const wstring& s) { dbg[n] = wcsdup(s.c_str()); }
#else
#define db(x, y)
#define DEBUG(x)
#endif
#ifdef _DEBUG
#include "earley_debug.h"
#endif

wstring format(wchar_t c) {
	if (!c) return L"eps";
	if (iswspace(c)) return L"ws";
	if (c == L'\r') return L"cr";
	if (c == L'\n') return L"lf";
	if (c == L'\t') return L"tab";
	return wstring(1,c);
}
bool samechar(wchar_t c, const wstring& s) {
	return s == L"alnum" ? iswalnum(c) : s == format(c);
}
template<typename C, typename T> bool has(const C& c, const T& t) {
	return c.find(t) != c.end();
}

typedef vector<wstring> rule;

size_t find(const vector<rule>& g, const wstring& nt) {
	return distance(g.begin(), lower_bound(g.begin(), g.end(), rule{nt}));
}

cfg* cfg_create(vector<rule> g, const wstring& S) {
	cfg &G = *new cfg;
	G.w = max_element(g.begin(), g.end(), [](const rule& x, const rule& y) {
			return x.size() < y.size(); })->size() + 1;
	const size_t w = G.w;
	size_t i, j, k;
	set<wstring> nulls;
	dig<size_t> &p = G.p, &c = G.c;

	g.push_back(rule{L"S'", S}), DEBUG(print_grammar(g)),
	nulls.emplace(wstring()), sort(g.begin(), g.end());

	for (i = 0; i < g.size(); ++i)
		if (g[i].size() == 1 || (g[i].size() == 2 && !g[i][1].size()))
			nulls.emplace(g[i][0]);
	for (size_t sz = 0; sz != nulls.size();) {
		sz = nulls.size();
		for (i = 0; i < g.size(); ++i) {
			if (has(nulls, g[i][0])) continue;
			for (j = 1; j < g[i].size(); ++j)
				if (!has(nulls, g[i][j])) break;
			if (j == g[i].size()) nulls.emplace(g[i][0]);
		}
	}
	DEBUG(print_nullables(nulls));
	for (i = 0; i < g.size(); ++i) {
		for (j = 1; j < g[i].size(); ++j) {
			if (has(nulls, g[i][j])) p.add(i*w + j, i*w + j + 1);
			if ((k=find(g, g[i][j]))==g.size())p.add(i*w+j, i*w+j);
			else for (;k < g.size() && g[k][0] == g[i][j]; ++k)
				p.add(i * w + j, k * w + 1),
				c.add(k * w + g[k].size(), i * w + j + 1);
		}
	}
	return nulls.clear(), G.g = g, p.close(), c.close(), &G;
}

void add_item(cfg& G, size_t d, size_t i, size_t k) {
	if (d % G.w == G.g[d / G.w].size())
		G.ec[k].emplace(G.len * d + i);
	else if (find(G.g, G.g[d / G.w][d % G.w]) < G.g.size())
		G.ep[k].emplace(G.len * d + i);
	else if (samechar(G.in[k], G.g[d / G.w][d % G.w]))
		add_item(G, d + 1, i, k + 1);
}

#define for_alt(it, s) \
	for (set<size_t>::const_iterator it = s.lower_bound((t - 1) * G.len); \
		it != s.end() && *it < t * G.len; ++it)

void cfg_parse(cfg &G, const wstring& in) {
	size_t len = G.len = (G.in = in).size() + 1, sp, sc;
	G.ep = new set<size_t>[in.size() + 1];
	G.ec = new set<size_t>[in.size() + 1];
	const size_t w = G.w;
	add_item(G, 1 + w * find(G.g, L"S'"), 0, 0);
	for (G.n = 0; G.n < len; ++G.n) {
		db(1, es2str(G, G.n));
		for (sp=sc=0; sp!=G.ep[G.n].size() || sc!=G.ec[G.n].size();) {
			sp = G.ep[G.n].size(), sc = G.ec[G.n].size();
			for (size_t d : G.ep[G.n])
				if (has(G.p.out, d / G.len))
					for (size_t t : G.p.out.at(d / G.len))
						add_item(G, t, G.n, G.n);
			for (size_t d : G.ec[G.n])
				if (has(G.c.out, d / G.len))
					for (size_t t : G.c.out.at(d / G.len)) {
						for_alt(it, G.ep[d % G.len])
							add_item(G, t,
								 *it%G.len,G.n);
						for_alt(it, G.ec[d % G.len])
							add_item(G, t,
								 *it%G.len,G.n);
					}
		}
	}
	DEBUG(for (size_t n = 0; n < len; ++n) wcout << es2str(G, n) << endl);
	delete[] G.ep; delete[] G.ec;
}

int main(int, char**) {
	setlocale(LC_ALL, "");
	wstring S(L"S"), T(L"T"), B(L"B"), a(L"a"), b(L"b"), ws(L"ws"), eps,
		A(L"A");
//	cfg g({ { S, a, S }, { S/*, eps*/ }}, S);
//	cfg &g = *cfg_create({ { S, a, S }, {S, a, eps} }, S);
	cfg &g = *cfg_create({ { S, S, T }, { S, a }, { B, eps }, { T, a, b },
		{ T, a } }, S);
	cfg_parse(g, L"aa");
	return 0;
}
