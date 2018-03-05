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
		if (out[x].emplace(y).second) in[y].emplace(x), ++sz;
	}
	bool has(const T& x, const T& y) {
		auto it = out.find(x);
		return it != out.end() && it->second.find(y) != it->second.end();
	}
	bool has_outgoing(const T& t) const { return out.find(t) != out.end(); }
	bool has_incoming(const T& t) const { return in.find(t) != in.end(); }
	const set<T>& outgoing(const T& t) const { return out.at(t); }
	const set<T>& incoming(const T& t) const { return in.at(t); }
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
	set<size_t> *es, *ep, *ec;
	wstring in;
	size_t n, len;

	wstring dr2str(size_t) const;
	wstring ei2str(size_t) const;
	wstring es2str(size_t) const;

	size_t find(const wstring& nt) const {
		size_t r = distance(g.begin(), lower_bound(g.begin(), g.end(), rule{nt}));
		return r;
       	}
	void add_item(size_t d, size_t i, size_t k) {
		wcout << L"add_item(" << ei2str(d) << L", " << i << L")" << endl;
		size_t rn = d / w, dot = d % w;
		if (find(g[rn][dot]) < g.size())
			(d%w == g[d/w].size() ? ec : ep)[k].emplace(len*d + i);
		else if (samechar(in[k], g[rn][dot]))
			add_item(d + 1, i, k + 1);
	};
	void print_cache(const dig<size_t>& d) const;
public:
	cfg(const vector<rule>&, const wstring&);
	void operator()(const wstring& in);
};
////////////////////////////////////////////////////////////////////////////////
void cfg::print_cache(const dig<size_t>& d) const {
	for (auto x : d.out) {
		wcout << dr2str(x.first) << L" => ";
		for (auto y : x.second) wcout << dr2str(y) << L" ";
		wcout << endl;
	}
}
cfg::cfg(const vector<rule>& _g, const wstring& S) : g(_g),
	w(max_element(g.begin(), g.end(), [](const rule& x, const rule& y) {
			return x.size() < y.size(); })->size() + 1) {
	g.push_back(rule{L"S'", S});
	sort(g.begin(), g.end());
	for (size_t i = 0, j, k; i < g.size(); ++i)
		for (j = 1; j < g[i].size(); ++j)
			if ((k = find(g[i][j])) == g.size()) p.add(i*w+j,i*w+j);
			else for (;k < g.size() && g[k][0] == g[i][j]; ++k)
				p.add(i * w + j, k * w + 1),
				c.add(k * w + g[k].size(), i * w + j);
	wcout << L"predictor cache:" << endl; print_cache(p);
	wcout << L"completer cache:" << endl; print_cache(c);
	p.close();
	wcout << L"predictor tc:" << endl; print_cache(p);
}
void cfg::operator()(const wstring& _in) {
	len = (in = _in).size() + 1;
	es = new set<size_t>[in.size() + 1];
	ep = new set<size_t>[in.size() + 1];
	ec = new set<size_t>[in.size() + 1];
	// eitem(d, i) to size_t: d*|a|+i i=e%|a| d=e/|a|
	add_item(w * find(L"S'"), 0, 0); 
	for (n = 0; n < len; ++n) {
		wcout << es2str(n);
		size_t sp, sc;
		do {
		sp = ep[n].size();
		sc = ec[n].size();
		for (size_t d : ep[n]) // predict
			if (p.has_outgoing(d / len))
				for (size_t t : p.outgoing(d / len))
					add_item(t * w + 1, n, n);
		for (size_t d : ec[n]) // complete
			if (c.has_outgoing(d / len))
				for (size_t t : c.outgoing(d / len))
					for (auto it=ep[d/len].lower_bound(t);
						it != ep[d / len].end() &&
						*it == t; ++it)
						add_item(w*(*it%len)+*it/len+1
								, d%len, n);
		} while (sp != ep[n].size() && sc != ec[n].size());
		wcout << es2str(n);
	}
	delete[] es;
	delete[] ep;
	delete[] ec;
}
////////////////////////////////////////////////////////////////////////////////
wstring cfg::dr2str(size_t d) const {
	const rule& r = g[d / w];
	wstringstream ss;
	ss << L'[' << r[0] << L" -> ";
	if (!(d % w)) ss << L"* ";
	for (size_t n = 1; n < r.size(); ++n) {
		if (n == d % w) ss << L"* ";
		ss << r[n] << L' ';
	}
	if (r.size() == d % w) ss << L"* ";
	return ss << L"]", ss.str();
}
wstring cfg::ei2str(size_t i) const {
	wstringstream ss;
	ss << L"{ " << dr2str(i / len) << L", " << i % len << L" }";
	return ss.str();
}
wstring cfg::es2str(size_t s) const {
	wstringstream ss;
	ss << L"E[" << s << L"]" << endl;
	for (size_t i : es[s]) ss << ei2str(i) << endl;
	for (size_t i : ep[s]) ss << ei2str(i) << endl;
	for (size_t i : ec[s]) ss << ei2str(i) << endl;
	return ss.str();
}
////////////////////////////////////////////////////////////////////////////////
int main(int, char**) {
	setlocale(LC_ALL, "");
	wstring S(L"S"), T(L"T"), B(L"B"), a(L"a"), b(L"b"), ws(L"ws"), eps,
		A(L"A");
	cfg g({ { S, S, T },
		{ S, a },
		{ B, eps },
		{ T, a, b },
		{ T, a }
		}, S);
	g(L"aa");
	return 0;
}
