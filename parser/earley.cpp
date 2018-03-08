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
	static const wchar_t eps[]=L"eps",ws[]=L"ws",cr[]=L"cr",lf[]=L"lf",tab[]=L"tab";
	if (!c)		return eps;
	if (iswspace(c))return ws;
	if (c == L'\r') return cr;
	if (c == L'\n') return lf;
	if (c == L'\t') return tab;
	return wstring(1, c);
}

bool samechar(wchar_t c, const wchar_t* s) {
	return !wcscmp(s, L"alnum") ? iswalnum(c) : s == format(c);
}

template<typename C, typename T> bool has(const C& c, const T& t) {
	return c.find(t) != c.end();
}

bool rlcmp(const vector<const wchar_t*>& x, const vector<const wchar_t*>& y) {
	int r;
	for (size_t i = 0, e = min(x.size(), y.size()); i < e; ++i)
		if (!(r = wcscmp(x[i], y[i]))) continue;
		else return r < 0;
	return x.size() == y.size() ? false : x.size() < y.size();
}

size_t find(const vector<vector<const wchar_t*>>& g, const wchar_t* nt) {
	return	distance(g.begin(),
		lower_bound(g.begin(), g.end(), vector<const wchar_t*>{nt}, rlcmp));
}

cfg* cfg_create(const vector<vector<wstring>>& g, const wchar_t* S) {
	vector<vector<const wchar_t*>> t;
	t.resize(g.size());
	for (size_t n = 0; n < g.size(); ++n) {
		t[n].resize(g[n].size());
		for (size_t k = 0; k < g[n].size(); ++k)
			t[n][k] = wcsdup(g[n][k].c_str());
	}
	return cfg_create(t, S);
}

cfg* cfg_create(const vector<vector<const wchar_t*>>& _g, const wchar_t* S) {
	cfg &G = *new cfg;
	size_t i, j, k;
	set<wstring> nulls;

	(G.g = _g).push_back({L"S'", S}); DEBUG(print_grammar(G.g));
	nulls.emplace(wstring()), G.w = 0, sort(G.g.begin(), G.g.end(), rlcmp);

	for (i = 0; i < G.g.size(); ++i) {
		G.w = max(G.w, G.g[i].size());
		if (G.g[i].size()==1 || (G.g[i].size()==2 && !wcslen(G.g[i][1])))
			nulls.emplace(G.g[i][0]);
	}
	++G.w;
	for (size_t sz = 0; sz != nulls.size();) {
		sz = nulls.size();
		for (i = 0; i < G.g.size(); ++i) {
			if (has(nulls, G.g[i][0])) continue;
			for (j = 1; j < G.g[i].size(); ++j)
				if (!has(nulls, G.g[i][j])) break;
			if (j == G.g[i].size()) nulls.emplace(G.g[i][0]);
		}
	}
	DEBUG(print_nullables(nulls));
	for (i = 0; i < G.g.size(); ++i) {
		for (j = 1; j < G.g[i].size(); ++j)
			if ((k = find(G.g, G.g[i][j])) != G.g.size()) {
				for (;k<G.g.size() && !wcscmp(G.g[k][0],G.g[i][j]); ++k)
					G.p.add(i*G.w + j, k * G.w + 1),
					G.c.add(k*G.w+G.g[k].size(), i*G.w+j+1);
				if (has(nulls, G.g[i][j]))
					G.p.add(i*G.w+j, i*G.w+j+1);
			} else G.p.add(i*G.w + j, i * G.w + j);
	}
	return nulls.clear(), G.p.close(), G.c.close(), &G;
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

void cfg_parse(cfg *_G, const wchar_t *in) {
	size_t sp, sc;
	cfg &G = *_G;
	G.len = wcslen(in) + 1;
	G.in = in;
	G.ep = new set<size_t>[G.len], G.ec = new set<size_t>[G.len];
	const size_t w = G.w;
	add_item(G, 1 + w * find(G.g, L"S'"), 0, 0);
	for (G.n = 0; G.n < G.len; ++G.n) {
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
								 *it%G.len,G.n),
							G.done[G.n*G.len+d%G.len].emplace(d/G.len);
							//G.done[G.n].emplace(d);
						for_alt(it, G.ec[d % G.len])
							add_item(G, t,
								 *it%G.len,G.n),
							G.done[G.n*G.len+d%G.len].emplace(d/G.len);
					}
		}
	}
	//DEBUG(for (size_t n=0; n<G.len; ++n) wcout << es2str(G, n) << endl);
	set<size_t> todel;
	for (size_t n = 0; n < G.len - 1; ++n) {
		G.ep[n].clear();
		for (size_t i : G.ec[n])
			if (!has(G.done[G.n*G.len+i%G.len], i/G.len))
				todel.emplace(i);
	//	for (size_t i : todel) G.ec[n].erase(i);
		todel.clear();
	}
	G.ep[G.len-1].clear();
	wcout << "SPPF:" << endl;
	for (auto t : G.done) {
		wcout << '(' << t.first%G.len << ',' << t.first/G.len << "): {";
		for (auto d : t.second) wcout << dr2str(G,d) << ' ';
		wcout << '}' << endl;
	}
//	DEBUG(for (size_t n = 0; n < G.len; ++n) wcout << es2str(G, n) << endl);

	delete[] G.ep; delete[] G.ec;
}
