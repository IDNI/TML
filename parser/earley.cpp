#include <vector>
#include <map>
#include <set>
#include <array>
#include <string>
#include <algorithm>
#include <iostream>
using namespace std;

typedef pair<size_t, size_t> interval;
typedef array<size_t, 4> eitem;
enum gitem_t { NULLABLE, TERMINAL, NONTERM };

struct gitem {
	gitem_t t;
	union { wchar_t sym;
		interval i; };
	gitem() {}
	void set(wchar_t s) { t = TERMINAL; sym = s; }
	void set(interval in, bool n) { i = in, t = n ? NULLABLE : TERMINAL; }
}; 

#define subset(x, y) includes(x.begin(), x.end(), y.begin(), y.end())

vector<vector<gitem>> cfg_compile(vector<vector<wstring>> g, wstring S) {
	vector<vector<gitem>> r;
	set<wstring> nulls;
	map<wstring, interval> alts;
	map<wstring, set<wstring>> in, out;
	map<wstring, set<wstring>>::const_iterator it, jt;
	map<wstring, interval>::const_iterator kt;
	wstring Z = L"Z";
	size_t s, i = 0, j = 0;

	nulls.emplace(), sort(g.begin(), g.end()), r.resize(g.size() + 1);
	while (Z <= g[g.size()-1][0]) Z += L'Z';
	g.push_back({Z, S});
	for (bool b = false; !b; ++i)
		if ((b = (i == g.size() - 1)) || g[i][0] != g[i+1][0])
			alts.emplace(g[i][0], interval(j, i + 1)), j = i + 1;
	for (i = 0; i < g.size(); ++i)
		for (r[i].resize(g[i].size() - 1), j = 1; j < g[i].size(); ++j)
			out[g[i][0]].emplace(g[i][j]),
			in[g[i][j]].emplace(g[i][0]);
iter:	s = r.size();
	for (const wstring& t : nulls)
		if ((it = in.find(t)) == in.end()) continue;
		else for (const wstring& y : it->second)
			if (	(jt = out.find(y)) != out.end() &&
				subset(jt->second, nulls)) nulls.emplace(y);
	if (s != r.size()) goto iter;
	for (i = 0; i < g.size(); ++i)
		for (j = 1; j < g[i].size(); ++j)
			if ((kt = alts.find(g[i][j])) != alts.end())
				r[i][j-1].set(kt->second,
					nulls.find(g[i][j]) != nulls.end());
			else r[i][j-1].set(g[i][j][0]);
	return r;
}

#define add_item(i, j) outs[i].emplace(j), ins[j].emplace(i), front.emplace(j)

bool cfg_parse(const vector<vector<gitem>>& g, const wchar_t* in) {
	eitem i = { 0, 0, g.size() - 1, 0 }, j;
	set<eitem> front;
	map<eitem, set<eitem>> ins, outs;
	set<eitem> s;
	map<eitem, set<eitem>>::const_iterator it, jt;

start:	gitem x = g[i[2]][i[3]];
	switch (x.t) {
	case NULLABLE:	j={i[0], i[1], i[2], i[3] + 1}, add_item(i, j);
	case NONTERM :	for (size_t n = x.i.first, k = n+x.i.second; n!=k; ++n)
				j = { i[0], 0, n, 0 }, add_item(i, j);
			break;
	case TERMINAL:	if (in[i[0]] == x.sym)
				j = { i[0] + 1, i[1] + 1, i[2], i[3] + 1 },
				add_item(i, j);
			else goto gc;
	}

cont:	if (front.empty()) return false;
	i = *front.begin(), front.erase(front.begin());
	if (front.empty() && i==eitem{ 0, 0, g.size()-1, g[s.size()-1].size() })
		return true;
	goto start;

gc:	size_t sz = s.size();
	s.emplace(i);
	for (const eitem& t : s)
		if ((it = ins.find(t)) == ins.end()) continue;
		else for (const eitem& y : it->second)
			if ((jt=outs.find(y))!=outs.end()&&subset(jt->second,s))
				s.emplace(y);
	if (sz != s.size()) goto gc;
	for (eitem x : s) {
		if ((it = outs.find(x)) != outs.end())
			for (const eitem& ox : it->second) ins[ox].erase(x);
		if ((it = ins.find(x)) != ins.end())
			for (const eitem& ix : it->second) outs[ix].erase(x);
		ins.erase(x), outs.erase(x), front.erase(x);
	}
	s.clear();
	goto cont;
}

int main(int, char**) {
	setlocale(LC_ALL, "");
	cfg_parse(cfg_compile({{L"S",L"a"}},L"S"),L"aa");
	return 0;
}
