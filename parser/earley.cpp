#include <string>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <functional>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <sstream>
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

wstring format(wchar_t c) {
	static const wchar_t 	eps[]=L"eps",ws[]=L"ws",cr[]=L"cr",lf[]=L"lf",
				tab[]=L"tab";
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
	return	distance(g.begin(), lower_bound(g.begin(), g.end(),
		vector<const wchar_t*>{nt}, rlcmp));
}

struct cfg {
	std::vector<std::vector<const wchar_t*>> g;
	dig<size_t> p, c, ep, ec;
	size_t w, n, len;
	std::map<size_t, std::set<size_t>> done;
	const wchar_t *in;
};

wstring dr2str(const cfg& G, size_t d) {
	const auto& g = G.g;
	const vector<const wchar_t*>& r = g[d / G.w];
	wstringstream ss;
	ss<<setw(3)<<d<<" "; if(!(d%G.w)) ss<<"* ";ss<<L'['<<r[0]<<" => ";
	for(size_t n=1;n<r.size();++n) {
		if (n == d%G.w) ss << "* ";
		if (*r[n]) ss << r[n] <<L' ';
		else ss << L"ε ";
	}
	if (r.size() == d % G.w) ss << "* ";
	return ss << L']', ss.str();
}

#ifdef _DEBUG
#include "earley_debug.h"
#endif

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

void cfg_delete(struct cfg* c) { delete c; }

cfg* cfg_create(const vector<vector<const wchar_t*>>& _g, const wchar_t* S) {
	cfg &G = *new cfg;
	size_t i, j, k;
	set<wstring> nulls;

	(G.g = _g).push_back({L"S'", S}); DEBUG(print_grammar(G.g));
	nulls.emplace(wstring()), G.w = 0, sort(G.g.begin(), G.g.end(), rlcmp);

	for (i = 0; i < G.g.size(); ++i) {
		G.w = max(G.w, G.g[i].size());
		if (G.g[i].size() == 1 || (G.g[i].size() == 2 && !*G.g[i][1]))
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
				for (;	k<G.g.size() &&
					!wcscmp(G.g[k][0],G.g[i][j]); ++k)
					G.p.add(i*G.w + j, k * G.w + 1),
					G.c.add(k*G.w+G.g[k].size(), i*G.w+j+1);
				if (has(nulls, G.g[i][j]))
					G.p.add(i*G.w+j, i*G.w+j+1);
			} else G.p.add(i*G.w + j, i * G.w + j);
	}
	return nulls.clear(), G.p.close(), G.c.close(), &G;
}

void add_item(cfg& G, size_t d, size_t i, size_t k) {
	const vector<const wchar_t*>& t = G.g[d / G.w];
	if (d % G.w == t.size()) G.ec.add(k, G.len * d + i);
	else if (G.ep.add(k, G.len*d+i), find(G.g, t[d%G.w]) == G.g.size()
		&& samechar(G.in[k], t[d % G.w]))
			add_item(G, d + 1, i, k + 1);
}

#define for_alt(it, s, t) \
	for (set<size_t>::const_iterator it = s.lower_bound((t - 1) * G.len); \
		it != s.end() && *it < t * G.len; ++it)
#define add_completed(i, t) \
	add_item(G,t,*it%G.len,G.n),G.done[G.n*G.len+i%G.len].emplace(i/G.len);

void cfg_parse(cfg *_G, const wchar_t *in) {
	size_t sp, sc;
	cfg &G = *_G;
	G.len = wcslen(in) + 1, G.in = in;
	const size_t w = G.w;
	add_item(G, 1 + w * find(G.g, L"S'"), 0, 0);
	for (G.n = 0; G.n < G.len; ++G.n) {
		for (sp=sc=0; 	sp!=G.ep.out[G.n].size() ||
				sc!=G.ec.out[G.n].size();) {
			sp = G.ep.out[G.n].size(), sc = G.ec.out[G.n].size();
			for (size_t i : G.ep.out[G.n])
				if (!has(G.p.out, i / G.len)) continue;
				else for (size_t j : G.p.out.at(i / G.len))
					add_item(G, j, G.n, G.n);
			for (size_t i : G.ec.out[G.n])
				if (!has(G.c.out, i / G.len)) continue;
				else for (size_t j : G.c.out.at(i / G.len)) {
					for_alt(it, G.ep.out[j % G.len], j)
						add_completed(i, j);
					for_alt(it, G.ec.out[j % G.len], j)
						add_completed(i, j);
				}
		}
	}
	//DEBUG(for (size_t n=0; n<G.len; ++n) wcout << es2str(G, n) << endl);
	wcout << "SPPF:" << endl;
	for (auto t : G.done) {
		wcout << '(' << t.first%G.len << ',' << t.first/G.len << "): {";
		for (auto d : t.second) wcout << dr2str(G,d) << ' ';
		wcout << '}' << endl;
	}
//	DEBUG(for (size_t n = 0; n < G.len; ++n) wcout << es2str(G, n) << endl);
}
