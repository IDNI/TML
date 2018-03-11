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
#else
#define DEBUG(x)
#endif

typedef size_t drule;
typedef size_t item;

wstring format(wchar_t c) {
	static const wchar_t 	eps[]=L"ε",ws[]=L"ws",cr[]=L"cr",lf[]=L"lf",
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

size_t find(const vector<vector<const wchar_t*> >& g, const wchar_t* nt) {
	return distance(g.begin(), lower_bound(g.begin(), g.end(),
		vector<const wchar_t*> {nt}, rlcmp));
}

size_t find(const vector<vector<const wchar_t*> >& g, size_t i, size_t j) {
	return (j == g[i].size() || !*g[i][j]) ? g.size() : find(g, g[i][j]);
}

struct cfg {
	std::vector<std::vector<const wchar_t*> > g;
	map<drule, set<drule> > p, c;
	size_t w;
};

wstring dr2str(const cfg& G, drule d) {
	const vector<const wchar_t*>& r = G.g[d / G.w];
	wstringstream ss;
	ss<<L'['<<r[0]<<" => ";
	for(size_t n = 1; n < G.g[d / G.w].size(); ++n)
		ss << (n == d%G.w ? "* " : "") << (*r[n] ? r[n] : L"ε") << ' ';
	return ss << (r.size() == d % G.w ? "* ]" : "]"), ss.str();
}

wostream& format_item(wostream& os, const cfg &G, size_t t, size_t len) {
	return	os << '[' << (t - t % len) / len - (t / (len * len)) * len
		<< ':' << t % len << ']' << dr2str(G, t / (len * len)) << endl;
}

void print_cache(const cfg& G, const dig<size_t>& d) {
	for (const auto& x : d.out) {
		wcout << dr2str(G, x.first) << "\t=>\t";
		for (auto y : x.second) wcout << dr2str(G,y)<<" ";
		wcout << endl;
	}
}

void print_grammar(const vector<vector<const wchar_t*>>& g) {
	for (auto& r : g) {
		wcout << r[0] << "\t=> ";
		if (r.size() == 1) wcout << L"ε ";
		else for (size_t i = 1; i < r.size(); ++i)
			wcout << (*r[i] ? r[i] : L"ε") << ' ';
		wcout << endl;
	}
}

cfg* cfg_create(const vector<vector<wstring> >& g, const wchar_t* S) {
	vector<vector<const wchar_t*> > t(g.size());
	for (size_t n = 0; n < g.size(); ++n) {
		t[n].resize(g[n].size());
		for (size_t k = 0; k < g[n].size(); ++k)
			t[n][k] = wcsdup(g[n][k].c_str());
	}
	return cfg_create(t, S);
}

void cfg_delete(struct cfg* c) { delete c; }

cfg* cfg_create(const vector<vector<const wchar_t*> >& _g, const wchar_t* S) {
	cfg &G = *new cfg;
	size_t i, j, k;
	set<wstring> nulls;
	dig<drule> p, c;
	auto f = [&nulls](const wchar_t* s) { return has(nulls, s); };

	(G.g = _g).push_back({L"S'", S}); DEBUG(print_grammar(G.g));
	G.w = 0, sort(G.g.begin(), G.g.end(), rlcmp);

	for (i = 0; i < G.g.size(); ++i)
		if (G.w = max(G.w, G.g[i].size()), !G.g[i].back())
			nulls.emplace(G.g[i][0]);

	for (size_t sz = 0; sz != nulls.size();)
		for (sz = nulls.size(), i = 0; i < G.g.size(); ++i)
			if (	!has(nulls, G.g[i][0]) &&
				all_of(&G.g[i][1], &G.g[i][G.g[i].size()], f))
				nulls.emplace(G.g[i][0]);

	for (i = 0; i < G.g.size(); ++i) {
		for (j = 1; j < G.g[i].size(); ++j)
			if ((k = find(G.g, i, j)) != G.g.size()) {
				for (;	k<G.g.size() &&
					!wcscmp(G.g[k][0],G.g[i][j]); ++k)
					add(p, i*G.w + j, k * G.w + 1),
					add(c, k*G.w+G.g[k].size(), i*G.w+j);
				if (has(nulls, G.g[i][j]))
					add(p, i*G.w+j, i*G.w+j+1);
			} else add(p, i*G.w + j, i * G.w + j);
	}
	return nulls.clear(), close(p.in, p.out, p),
	close(c.in, c.out, c), G.c = move(c.out), G.p = move(p.out), &G;
}

bool push(map<size_t, set<item> >& q, size_t x, size_t y) {
	bool r = !has(q, x);
	return q[x].emplace(x + y).second || r;
}

void cfg_parse(const cfg &G, const wchar_t* in) {
	size_t m, sz = 1, _sz = 0;
	const size_t len = wcslen(in) + 1, w = G.w, l2 = len * len;
	map<size_t, set<item> > q;
	map<size_t, set<item> >::const_iterator it;
	set<item>::const_iterator lb;
	q[0].emplace(l2 * (1 + w * find(G.g, L"S'")));
	for (size_t j = 0; j < len; ++j) {
		_sz = 0;
		while (_sz != sz) {
			_sz = sz;
			for (const item t : q[j]) {
				const size_t d = t / l2;
				if (	d % w < G.g[d / w].size() && j < len &&
					find(G.g, d / w, d % w) == G.g.size()) {
					if (samechar(in[j], G.g[d/w][d%w]) &&
						push(q, j + 1, t - j + l2))
						++sz;
					continue;
				}
				if (has(G.p, d))
					for (const drule c : G.p.at(d))
						if (push(q,j,c*l2+len*j)) ++sz;
				if (!has(G.c, d)) continue;
				for (const drule c : G.c.at(d))
					if ((it=q.find(m=(t-j)/len-d*len))!=q.end())
						for(lb=it->second.lower_bound(c*l2);
						    lb!=it->second.end()&&*lb<(c+1)*l2;
						    ++lb)
							if(push(q,j,*lb-*lb%len+l2))++sz;
			}
		}
	}
	for (auto x : q) for (auto y : x.second) format_item(wcout, G, y, len);
}
