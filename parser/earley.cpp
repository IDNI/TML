#include <vector>
#include <map>
#include <set>
#include <array>
#include <string>
#include <algorithm>
#include <iostream>
#include <cassert>
#include <climits>
#include <sstream>
#include <iterator>
#include <cstring>
#include <fstream>
using namespace std;

typedef array<size_t, 2> interval;
enum gitem_t { NULLABLE, TERMINAL, NONTERM };
#define subset(x, y) includes(x.begin(), x.end(), y.begin(), y.end())

struct gitem {
	gitem_t t;
	//union {
		wchar_t ch; interval i; 
	//};
	void set(wchar_t s) { t = TERMINAL; ch = s; }
	void set(interval in, bool n) { i = in; t = n ? NULLABLE : NONTERM; }
}; 
struct eitem {
	size_t end, nt, len, alt, dot;
	eitem(	size_t end = 0, size_t nt = 0, size_t len = 0, size_t alt = 0,
		size_t dot = 0):end(end),nt(nt),len(len),alt(alt),dot(dot) { assert(end >= len); }
	eitem(const vector<vector<gitem>>& g, size_t end, size_t len,
		size_t alt, size_t dot):eitem(end, g[alt].size()==dot? UINT_MAX:
			g[alt][dot].t != TERMINAL ? g[alt][dot].i[0] : UINT_MAX
			, len, alt, dot) { }
};
typedef pair<vector<vector<gitem>>, pair<size_t, const wchar_t*>*> compiled_cfg;
////////////////////////////////////////////////////////////////////////////////
#define cmp_(t) x.t!=y.t
#define cmp(t) cmp_(t)?x.t<y.t
bool operator<(const eitem& x, const eitem& y) {
	return cmp(end):cmp(nt):cmp(len):cmp(alt):cmp(dot):false; }
bool operator!=(const eitem& x, const eitem& y) {
	return cmp_(end)||cmp_(nt)||cmp_(len)||cmp_(alt)||cmp_(dot); }

wstring format(const compiled_cfg& g, size_t i, size_t j) {
	wstringstream ss;
	wstring r;
	gitem t;
	for (size_t n = 0; n < g.first[i].size(); ++n) {
		t = g.first[i][n];
		if (n == j) ss << "* ";
		if (t.t == TERMINAL) ss << L'\'' << (t.ch ? t.ch : L'ε') << L"' ";
		else ss << g.second[t.i[0]].second << ' ';
	}
	if (j == g.first[i].size()) ss << "* ";
	r = ss.str();
	return r;
}
wstring format(const compiled_cfg& g, eitem i) {
	wstringstream ss;
	wstring r;
	ss << '[' << i.end-i.len << ':' << i.end << "] " << format(g, i.alt, i.dot);
	if (i.nt != UINT_MAX) ss << " (" << g.second[i.nt].second << ')';
	r = ss.str();
	return r;
}
////////////////////////////////////////////////////////////////////////////////
compiled_cfg cfg_compile(vector<vector<wstring>> g, wstring S) {
	compiled_cfg r;
	set<wstring> nulls;
	map<wstring, interval> alts;
	map<wstring, set<wstring>> in, out;
	wstring Z = L"Z";
	size_t s, i = 0, j = 0;
	r.second = new pair<size_t, const wchar_t*>[g.size()+1];

//	if (!is_sorted(g.begin(), g.end())) throw 0;
	nulls.emplace(), sort(g.begin(), g.end()), r.first.resize(g.size() + 1);
	wcout << g.size() << endl;
	for (auto x : g) { for (auto y : x) wcout << y << ' '; wcout << endl; }
	assert(g[g.size()-1].size());
	while (Z <= g[g.size()-1][0])
		Z += Z;
	g.push_back({Z, S});

	for (bool b = false; !b; ++i)
		if ((b = (i == g.size() - 1)) || g[i][0] != g[i+1][0])
			alts.emplace(g[i][0], interval{{j, i + 1}}), j = i + 1;
	for (auto a : alts)
		r.second[a.second[0]].second = wcsdup(a.first.c_str());
	for (i = 0; i < g.size(); ++i)
		for (r.first[i].resize(g[i].size()-1), j=1; j<g[i].size(); ++j)
			out[g[i][0]].emplace(g[i][j]),
			in[g[i][j]].emplace(g[i][0]);

iter:	s = nulls.size();
	for (const wstring& t : nulls)
		if (auto it = in.find(t); it == in.end()) continue;
		else for (const wstring& y : it->second)
			if (auto jt = out.find(y); jt != out.end() &&
				subset(jt->second, nulls)) nulls.emplace(y);
	if (s != nulls.size()) goto iter;

	wstring l = g[0][0];
	for (i = j = 0;; l = g[j = i][0]) {
		while (i < g.size() && g[i][0] == l) r.second[i++].first = j;
		if (i == g.size()) break;
	}
	for (i = 0; i < g.size(); ++i)
		for (j = 1; j < g[i].size(); ++j)
			if (auto kt = alts.find(g[i][j]); kt != alts.end())
				r.first[i][j-1].set(kt->second,
					nulls.find(g[i][j]) != nulls.end());
			else r.first[i][j-1].set(g[i][j][0]);
	return r;
}

bool cfg_parse(const compiled_cfg& G, const wchar_t* in) {
	auto &g = G.first;
	const eitem f(g,wcslen(in),wcslen(in),g.size()-1,g[g.size()-1].size()),
		st(g, 0, 0, G.first.size() - 1, 0);
	eitem i = st, j, k;
	set<eitem> front, s;
	map<eitem, set<eitem>> ins, outs;
	size_t nt;
	gitem x;
#define add_item(i, j) \
	outs[i].emplace(j), ins[j].emplace(i), front.emplace(j), front.erase(i) \
	, (wcout<<"add_item from "<<format(G,i) << " to " <<format(G,j)<<endl)

start:	if (g[i.alt].size() == i.dot) {
		auto it = outs.lower_bound(eitem(i.end - i.len, nt = G.second[i.alt].first, 0, 0, 0));
		for (;	it != outs.end() && it->first.end == i.end - i.len &&
			it->first.nt == nt; ++it)
			k = it->first,
			j = eitem(g, i.end, k.len+i.len, k.alt, k.dot + 1),
			add_item(i, k), add_item(k, j);
		goto cont;
	}
	x = g[i.alt][i.dot];
	switch (x.t) {
	case NULLABLE:	j = eitem(g,i.end, i.len, i.alt, i.dot + 1), add_item(i, j);
	case NONTERM :	for (size_t n = x.i[0], k = x.i[1]; n != k; ++n)
				j = eitem(g,i.end, 0, n, 0), add_item(i, j);
			break;
	case TERMINAL:	if (!x.ch) break;
			if (in[i.end] != x.ch) goto gc;
			j = eitem(g, i.end+1, i.len+1, i.alt, i.dot+1),
			add_item(i, j);
	}

cont:	if (front.empty() || outs.find(st) == outs.end()) return false;
	if (ins.find(f) != ins.end()) return true;
	i = *front.begin(), front.erase(front.begin());
	wcout << "processing: " << format(G, i) << endl;
	{ set<wstring> dbg;
	for (auto x : ins) for (auto y : x.second) dbg.emplace(format(G, y) + L" -> " + format(G, x.first));
	for (auto x : outs) for (auto y : x.second) dbg.emplace(format(G, x.first) + L" -> " + format(G, y));
	for (auto x : dbg) wcout << x << endl; }
	goto start;

gc:	size_t sz = s.size();
	s.emplace(i);
	for (const eitem& t : s)
		if (auto it = ins.find(t); it == ins.end())
			for (const eitem& y : it->second)
				if (	auto jt=outs.find(y); jt!=outs.end() &&
					subset(jt->second,s)) s.emplace(y);
	if (sz != s.size()) goto gc;
	for (eitem x : s) {
		if (auto it = outs.find(x); it != outs.end())
			for (const eitem& ox : it->second) ins[ox].erase(x);
		if (auto it = ins.find(x); it != ins.end())
			for (const eitem& ix : it->second) outs[ix].erase(x);
		ins.erase(x), outs.erase(x), front.erase(x);
	}
	s.clear();
	goto cont;
}
////////////////////////////////////////////////////////////////////////////////
wstring& trim(wstring& s) {
	s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int ch) { return !iswspace(ch); }));
	s.erase(std::find_if(s.rbegin(), s.rend(), [](int ch) { return !iswspace(ch); }).base(), s.end());
	return s;
}

int main(int argc, char** argv) {
	setlocale(LC_ALL, "");
	assert(argc == 3);
	wstring w, arg;
	wifstream fg(argv[1]), fi(argv[2]);
	for (wstring line; getline(fi, line); arg += line);
	wcout<<"arg: " << arg << endl;
	vector<vector<wstring>> g;
	for (wstring line; getline(fg, line);) {
		if (!line.size()) continue;
		wistringstream ss(line);
		g.emplace_back();
		while (ss >> w) g.back().push_back(trim(w));
		if (g.back().size() == 1) g.back().emplace_back();
	}
	for (auto x : g) {
		for (auto y : x) wcout << y << ' ';
		wcout << endl;
	}
	if (cfg_parse(cfg_compile(g, L"S"), arg.c_str())) wcout << "pass";
	else wcout << "fail";
	//vector<vector<wstring>> g{{L"S",L"a"}};
//	assert(cfg_parse(cfg_compile(g,L"S"),L"a"));
//	assert(!cfg_parse(cfg_compile(g,L"S"),L"aa"));
//	assert(!cfg_parse(cfg_compile(g,L"S"),L"b"));
	return 0;
}
