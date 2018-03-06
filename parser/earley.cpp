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
		if (*ix < *iy) ++ix; else if (*ix > *iy) ++iy; else return true;
	return false;	
} 
////////////////////////////////////////////////////////////////////////////////
template<typename T>
class dig { // digraph
public:
	map<T, set<T>> in, out;
	size_t sz = 0;
	void add(const T& x, const T& y) {
		if (out[x].emplace(y).second) in[y].emplace(x), out[y], ++sz;
	}
	bool has(const T& x, const T& y) const {
		auto it = out.find(x);
		return it != out.end() && has(it->second, y);
	}
	bool has_in (const T& t) const { return ::has(in, t);  }
	bool has_out(const T& t) const { return ::has(out, t); }
	const set<T>& incoming(const T& t) const { return in.at(t);  }
	const set<T>& outgoing(const T& t) const { return out.at(t); }
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
class cfg {
	vector<rule> g;
	dig<size_t> p, c;
	const size_t w;
	set<size_t> *ep, *ec;
	set<wstring> nulls;
	wstring in;
	size_t n, len;

	wstring dr2str(size_t) const;
	wstring ei2str(size_t) const;
	wstring es2str(size_t) const;

	size_t find(const wstring& nt) const {
		return distance(g.begin(),
				lower_bound(g.begin(), g.end(), rule{nt}));
       	}
	void print_cache(const dig<size_t>& d) const {
		for (auto x : d.out) {
			wcout << dr2str(x.first) << L" => ";
			for (auto y : x.second) wcout << dr2str(y) << L" ";
			wcout << endl;
		}
	}
	void add_item(size_t d, size_t i, size_t k);
	void predict(size_t);
	void complete(size_t);
public:
	cfg(const vector<rule>&, const wstring&);
	void operator()(const wstring& in);
};
////////////////////////////////////////////////////////////////////////////////
cfg::cfg(const vector<rule>& _g, const wstring& S) : g(_g),
	w(max_element(g.begin(), g.end(), [](const rule& x, const rule& y) {
			return x.size() < y.size(); })->size() + 1) {
	size_t i, j, k;
	set<wstring> nulls;

	g.push_back(rule{L"S'", S});
	sort(g.begin(), g.end());

	for (i = 0; i < g.size(); ++i)
		if (g[i].size() == 1)
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
	for (i = 0; i < g.size(); ++i)
		for (j = 1; j < g[i].size(); ++j)
			if ((k = find(g[i][j])) == g.size()) p.add(i*w+j,i*w+j);
		else for (;k < g.size() && g[k][0] == g[i][j]; ++k) {
			p.add(i * w + j, k * w + 1);
			c.add(k * w + g[k].size(), i * w + j + 1);
		}
	p.close(), c.close();
	wcout << L"predictor tc:" << endl; print_cache(p);
	wcout << L"completer tc:" << endl; print_cache(c);
}
void cfg::add_item(size_t d, size_t i, size_t k) {
	db(1, dr2str(d));
	db(2, ei2str(len*d+i));
	if (d % w == g[d / w].size() || !g[d / w][d % w].size())
		ec[k].emplace(len * d + i);
	else if (find(g[d / w][d % w]) < g.size()) {
		db(3, g[d / w][d % w]);
		ep[k].emplace(len * d + i).second;
	}
	else if (samechar(in[k], g[d / w][d % w]))
		add_item(d + 1, i, k + 1);
}
void cfg::predict(size_t d) {
	db(1, ei2str(d));
	db(2, g[(d / len) / w][(d / len) % w]);
	if (has(nulls, g[(d / len) / w][(d / len) % w]))
		add_item((d / len + 1) * len + d % len, n, n);
	if (!p.has_out(d / len)) return;
	for (size_t t : p.outgoing(d / len)) {
		db(2, dr2str(t));
		add_item(t, n, n);
	}
}
void cfg::complete(size_t d) {
	db(1, ei2str(d));
	if (!c.has_out(d / len)) return;
	for (size_t t : c.outgoing(d / len)) {
		db(2, dr2str(t)), db(3, dr2str(t - 1));
		for (auto it = ep[d % len].lower_bound((t - 1) * len);
			it != ep[d % len].end() && *it == (t - 1) * len; ++it) {
			db(4, ei2str(*it));
			add_item(t, *it % len, n);
		}
	}
}
void cfg::operator()(const wstring& _in) {
	len = (in = _in).size() + 1;
	ep = new set<size_t>[in.size() + 1];
	ec = new set<size_t>[in.size() + 1];
	add_item(1 + w * find(L"S'"), 0, 0); 
	for (n = 0; n < len; ++n) {
		db(1, es2str(n));
		size_t sp, sc;
		do {
			sp = ep[n].size();
			sc = ec[n].size();
			for (size_t d : ep[n]) predict(d);
			for (size_t d : ec[n]) complete(d);
		} while (sp != ep[n].size() && sc != ec[n].size());
	}
	for (n = 0; n < len; ++n) wcout << es2str(n) << endl;
	delete[] ep; delete[] ec;
}
////////////////////////////////////////////////////////////////////////////////
wstring cfg::dr2str(size_t d) const {
	const rule& r = g[d / w];
	wstringstream ss;
	ss << d << L':'; if (!(d % w)) ss << L"* "; ss << L'[' << r[0]<<L" -> ";
	for(size_t n=1; n<r.size(); ++n){if (n==d%w) ss<<L"* "; ss<<r[n]<<L' ';}
	if (r.size() == d % w) ss << L"* ";
	return ss << L"]", ss.str();
}
wstring cfg::ei2str(size_t i) const {
	wstringstream ss;
	ss << i << L':' << L"{ " << dr2str(i / len) << L", " << i % len <<L" }";
	return ss.str();
}
wstring cfg::es2str(size_t s) const {
	wstringstream ss;
	ss<<L"\tP["<<s<<L"]"<<endl; for (size_t i:ep[s]) ss<<ei2str(i)<<endl;
	ss<<L"\tC["<<s<<L"]"<<endl; for (size_t i:ec[s]) ss<<ei2str(i)<<endl;
	return ss.str();
}
////////////////////////////////////////////////////////////////////////////////
int main(int, char**) {
	setlocale(LC_ALL, "");
	wstring S(L"S"), T(L"T"), B(L"B"), a(L"a"), b(L"b"), ws(L"ws"), eps,
		A(L"A");
	cfg g({ { S, a, S }, { S/*, eps*/ }}, S);
//	cfg g({ { S, S, T }, { S, a }, { B, eps }, { T, a, b }, { T, a } }, S);
	g(L"aaaa");
	return 0;
}
