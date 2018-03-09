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
#include <cassert>
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

typedef size_t drule;
typedef size_t item;
////////////////////////////////////////////////////////////////////////////////////////////////////
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
bool samechar(wchar_t c, const wchar_t* s) {return !wcscmp(s, L"alnum")?iswalnum(c):s==format(c);} 
template<typename C, typename T> bool has(const C& c, const T& t) { return c.find(t) != c.end(); }
bool rlcmp(const vector<const wchar_t*>& x, const vector<const wchar_t*>& y) {
	int r;
	for (size_t i = 0, e = min(x.size(), y.size()); i < e; ++i)
		if (!(r = wcscmp(x[i], y[i]))) continue;
		else return r < 0;
	return x.size() == y.size() ? false : x.size() < y.size();
}
size_t find(const vector<vector<const wchar_t*>>& g, const wchar_t* nt) {
	return distance(g.begin(), lower_bound(g.begin(), g.end(),
		vector<const wchar_t*>{nt}, rlcmp));
}
size_t find(const vector<vector<const wchar_t*>>& g, size_t i, size_t j) {
	return (j == g[i].size() || !*g[i][j]) ? g.size() : find(g, g[i][j]);
}
////////////////////////////////////////////////////////////////////////////////////////////////////
struct cfg {
	std::vector<std::vector<const wchar_t*>> g;
	dig<drule> p, c;
	size_t w;
};

wstring dr2str(const cfg& G, drule d) {
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
void print_item(const cfg &G, size_t t, size_t len) {
	wcout<<'['<<(t-t%len)/len-(t/(len*len))*len<<':'<<t%len<<']'<<dr2str(G, t/(len*len))<<endl;
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
////////////////////////////////////////////////////////////////////////////////////////////////////
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
			if ((k = find(G.g, i, j)) != G.g.size()) {
				for (;	k<G.g.size() &&
					!wcscmp(G.g[k][0],G.g[i][j]); ++k)
					add(G.p, i*G.w + j, k * G.w + 1),
					add(G.c, k*G.w+G.g[k].size(), i*G.w+j);
				if (has(nulls, G.g[i][j]))
					add(G.p, i*G.w+j, i*G.w+j+1);
			} else add(G.p, i*G.w + j, i * G.w + j);
	}
	return nulls.clear(), close(G.p.in, G.p.out, G.p),
	close(G.c.in, G.c.out, G.c), &G;
}

bool push(map<size_t, set<item>>& q, size_t x, size_t y) {
	bool r = !has(q, x);
	return q[x].emplace(x + y).second || r;
}

void cfg_parse(const cfg &G, const wchar_t* in) {
	size_t len = wcslen(in) + 1, sz = 1, _sz = 0;
	const size_t w = G.w, l2 = len * len;
	map<size_t, set<item>> q;
	q[0].emplace(len * len * (1 + w * find(G.g, L"S'")));
	for (size_t j = 0; j < len; ++j) {
		_sz = 0;
		while (_sz != sz) {
			_sz = sz;
			for (const item t : q[j]) {
				const size_t d = t / l2;
				if (	d % w < G.g[d / w].size() && j < len &&
					find(G.g, d / w, d % w) == G.g.size()) {
					if (	samechar(in[j], G.g[d / w][d % w]) &&
						push(q, j + 1, t - j + l2))
						++sz;
					continue;
				}
				if (has(G.p.out, d))
					for (const drule c : G.p.out.at(d))
						if (push(q, j, len*(c*len+j))) ++sz;
				if (has(G.c.out, d))
					for (const size_t s : q[(t - j) / len - d * len])
						for (const drule c : G.c.out.at(d))
							if (	c == s / l2 &&
								push(q, j, s - s % len + l2))
								++sz;
			}
		}
	}
	for (auto x : q) for (auto y : x.second) print_item(G,y, len);
}
