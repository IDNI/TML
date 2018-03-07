// -std=c++1z for std::sort and std::max_element
#include <string>
#include <iostream>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <functional>
#include <sstream>
#include <algorithm>
#include <iomanip>
using namespace std;
////////////////////////////////////////////////////////////////////////////////
#define DEBUG
#ifdef DEBUG
typedef const wchar_t* wsptr;
wsptr dbg[10];
void db(size_t n, const wstring& s) { dbg[n] = wcsdup(s.c_str()); }
#else
#define db(x, y)
#endif
////////////////////////////////////////////////////////////////////////////////
typedef vector<wstring> rule;
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
template<typename T> bool have_common(const T& x, const T& y) {
	for (auto ix = x.begin(), iy = y.begin(); ix!=x.end() && iy!=y.end();)
		if (*ix < *iy) ++ix; else if (*ix>*iy) ++iy; else return true;
	return false;
}
////////////////////////////////////////////////////////////////////////////////
template<typename T>
class dig { // digraph
public:
	map<T, set<T>> in, out;
	size_t sz = 0;
	void add(const T& x, const T& y) {
		if (out[x].emplace(y).second) in[y].emplace(x), ++sz;
	}
	bool has(const T& x, const T& y) const {
		auto it = out.find(x);
		return it != out.end() && has(it->second, y);
	}
	bool has_in (const T& t) const		{ return ::has(in, t);  }
	bool has_out(const T& t) const		{ return ::has(out, t); }
	const set<T>& incoming(const T& t) const{ return in.at(t);  }
	const set<T>& outgoing(const T& t) const{ return out.at(t); }
	void close() {
		for (size_t s = 0; s != sz;) {
			s = sz;
			for (const auto& x : out)
				for (const auto& y : in)
					if (have_common(x.second, y.second))
						add(x.first, y.first);
		}
	}
};
////////////////////////////////////////////////////////////////////////////////
struct cfg {
	vector<rule> g;
	dig<size_t> p, c;
	size_t w;
	set<size_t> *ep, *ec;
	set<wstring> nulls;
	wstring in;
	size_t n, len;
};
////////////////////////////////////////////////////////////////////////////////
wstring dr2str(const cfg& G, size_t d) {
	const auto& g = G.g;
	const rule& r = g[d / G.w];
	wstringstream ss;
	ss<<setw(3)<<d<<" "; if(!(d%G.w)) ss<<"* ";ss<<L'['<<r[0]<<" => ";
	for(size_t n=1;n<r.size();++n) {
		if (n == d%G.w) ss << "* ";
		if (r[n].size()) ss << r[n] <<L' ';
		else ss << L"ε ";
	}
	if (r.size() == d % G.w) ss << "* ";
	return ss << L']', ss.str();
}
wstring ei2str(const cfg& G, size_t i) {
	wstringstream ss;
	ss<<setw(4)<<i<<" {"<<left<<setw(G.w*4)<<dr2str(G,i/G.len);
	return ss << ',' << i % G.len << " }", ss.str();
}
wstring es2str(const cfg& G, size_t s) {
	wstringstream ss;
	for (size_t i : G.ep[s])ss << "P[" << s << "]: " << ei2str(G, i) <<endl;
	for (size_t i : G.ec[s])ss << "C[" << s << "]: " << ei2str(G, i) <<endl;
	return ss.str();
}
void print_cache(const cfg& G, const dig<size_t>& d) {
	for (const auto& x : d.out) {
		wcout<<left<<setw(G.w*4)<< dr2str(G, x.first) << "\t=>\t";
		for (auto y:x.second)wcout<<left<<setw(G.w*4)<<dr2str(G,y)<<" ";
		wcout << endl;
	} wcout << endl;
}
////////////////////////////////////////////////////////////////////////////////
size_t find(const vector<rule>& g, const wstring& nt) {
	return distance(g.begin(),
			lower_bound(g.begin(), g.end(), rule{nt}));
}

cfg* cfg_create(vector<rule> g, const wstring& S) {
	cfg &G = *new cfg;
	G.w = max_element(g.begin(), g.end(), [](const rule& x, const rule& y) {
			return x.size() < y.size(); })->size() + 1;
	const size_t w = G.w;
	size_t i, j, k;
	set<wstring> nulls;
	dig<size_t> &p = G.p, &c = G.c;
	g.push_back(rule{L"S'", S});

	for (const rule& r : g) {
		wcout << r[0] << "\t => ";
		if (r.size() == 1) wcout << L"ε ";
		else for (i = 1; i < r.size(); ++i)
			if (r[i].size()) wcout << r[i] << L' ';
			else wcout << L"ε ";
		wcout << endl;
	}
	nulls.emplace(wstring());
	wcout << endl; sort(g.begin(), g.end());
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
	wcout << "nullables: ";
	for (wstring d : nulls) if (d.size()) wcout<<d<<' '; else wcout<<L"ε ";
	wcout << endl;

	for (i = 0; i < g.size(); ++i) {
		for (j = 1; j < g[i].size(); ++j) {
			if (has(nulls, g[i][j]))
				p.add(i * w + j, i * w + j + 1);
			if ((k = find(g, g[i][j])) == g.size())
				p.add(i*w+j,i*w+j);
			else for (;k < g.size() && g[k][0] == g[i][j]; ++k) {
				p.add(i * w + j, k * w + 1);
				c.add(k * w + g[k].size(), i * w + j + 1);
			}
		}
	}
	G.g = g, p.close(), c.close();
	wcout << "predictor tc:" << endl; print_cache(G,p);
	wcout << "completer tc:" << endl; print_cache(G,c);
	return &G;
}

void add_item(cfg& G, size_t d, size_t i, size_t k) {
	size_t len = G.len, w = G.w;
	db(1, dr2str(G,d));
	db(2, ei2str(G,len*d+i));
	auto &g = G.g;
	if (d % w == g[d / w].size())
		G.ec[k].emplace(len * d + i);
	else if (find(g, g[d / w][d % w]) < g.size()) {
		db(3, g[d / w][d % w]);
		G.ep[k].emplace(len * d + i);
	}
	else if (samechar(G.in[k], g[d / w][d % w]))
		add_item(G, d + 1, i, k + 1);
}

void predict(cfg &G, size_t d) {
	db(1, ei2str(G, d));
	db(2, G.g[(d / G.len) / G.w][(d / G.len) % G.w]);
	wcout << G.n << "\tpredicting " << dbg[1] << endl;
	if (!G.p.has_out(d / G.len)) return;
	for (size_t t : G.p.outgoing(d / G.len)) {
		db(2, dr2str(G, t));
		wcout << "predict: calling additem with " << dbg[2] << endl;
		add_item(G, t, G.n, G.n);
	}
}

void complete(cfg &G, size_t d) {
	db(1, ei2str(G, d));
	wcout << G.n << "\tcompleting " << dbg[1] << endl;
	if (!G.c.has_out(d / G.len)) return;
	for (size_t t : G.c.outgoing(d / G.len)) {
		db(2, dr2str(G, t)), db(3, dr2str(G, t - 1));
		for (auto it = G.ep[d % G.len].lower_bound((t - 1) * G.len);
			it != G.ep[d % G.len].end() && *it<(t)*G.len; ++it) {
			db(4, ei2str(G, *it));
			wcout << "complete: calling additem with " << dbg[2] <<
				" pos " << (*it / G.len) % G.w <<
				" due to *it = " << dbg[4] << endl;
			add_item(G, t, (*it % G.len), G.n);
		}
		for (auto it = G.ec[d % G.len].lower_bound((t - 1) * G.len);
			it != G.ec[d % G.len].end() && *it<(t)*G.len; ++it) {
			db(4, ei2str(G, *it));
			wcout << "complete: calling additem with " << dbg[2] <<
				" pos " << (*it / G.len) % G.w <<
				" due to *it = " << dbg[4] << endl;
			add_item(G, t, (*it % G.len), G.n);
		}
	}
}

void cfg_parse(cfg &G, const wstring& in) {
	wcout << "in: " << in << endl;
	size_t len = G.len = (G.in = in).size() + 1;
	auto ep = G.ep = new set<size_t>[in.size() + 1];
	auto ec = G.ec = new set<size_t>[in.size() + 1];
	const size_t w = G.w;
	add_item(G, 1 + w * find(G.g, L"S'"), 0, 0);
	for (G.n = 0; G.n < len; ++G.n) {
		db(1, es2str(G, G.n));
		size_t sp, sc;
		do {
			sp = ep[G.n].size();
			sc = ec[G.n].size();
			for (size_t d : ep[G.n]) predict(G, d);
			for (size_t d : ec[G.n]) complete(G, d);
		} while (sp != G.ep[G.n].size() || sc != G.ec[G.n].size());
	}
	for (size_t n = 0; n < len; ++n) wcout << es2str(G, n) << endl;
	delete[] G.ep; delete[] G.ec;
}
////////////////////////////////////////////////////////////////////////////////
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
