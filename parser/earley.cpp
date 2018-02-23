// a yet nonworking earley-scott parsing alog impl
// -std=c++1z (for std::variant)

#include <map>
#include <set>
#include <utility>
#include <vector>
#include <variant>
#include <cwctype>
#include <cassert>
#include <iostream>

using namespace std;
////////////////////////////////////////////////////////////////////////////////
typedef vector	<wstring>				prod;
typedef tuple	<wstring, prod, size_t>			drule;
typedef tuple	<variant<wstring,drule>, size_t, size_t>node;
typedef variant	<nullptr_t, node>			pnode;
typedef tuple	<drule, size_t, pnode>			eitem;
typedef map	<wstring, set<prod>>			cfg;
typedef map	<node, set<pair<pnode, pnode>>>		sppf;
typedef map	<wstring, set<eitem>>			eset;
////////////////////////////////////////////////////////////////////////////////
#define isnull(x) holds_alternative<nullptr_t>(x)
#define rl(x) get<drule>(x)
wstring afterdot(const drule& d) {
	const prod& p = get<prod>(d);
	return get<size_t>(d) >= p.size() ? wstring() : p[get<size_t>(d)];
}
eitem next(const eitem& e) {
	eitem r(e);
	return ++get<size_t>(rl(r)), r;
}
template<typename C, typename V> bool has(const C& x, const V& y) {
	return x.find(y) != x.end();
}
bool nonterm(const cfg& g, const drule& d) { return has(g, afterdot(d)); }
////////////////////////////////////////////////////////////////////////////////
wstring format(wchar_t c) {
	if (!c) return L"eps";
	if (iswspace(c)) return L"ws";
	if (c == L'\r') return L"cr";
	if (c == L'\n') return L"lf";
	if (c == L'\t') return L"tab";
	wstring r(1, c);
	return r.push_back(0), r;
}
bool samechar(wchar_t c, const wstring& s) {
	if (s == L"alnum") return iswalnum(c);
	return s == format(c);
}
wostream& operator<<(wostream& os, const pnode&);
wostream& operator<<(wostream& os, const node&);
wostream& operator<<(wostream& os, const drule&);
wostream& operator<<(wostream& os, const wstring& s) {
	return s.size() < 1 ? os << format(s[0]) : os << s.c_str();
}
#include "generic-formatting.hpp"
wostream& operator<<(wostream& os, const node& n) {
	os << L"< ";
	if (holds_alternative<wstring>(get<0>(n))) os<<get<wstring>(get<0>(n));
	else os << rl(get<0>(n));
	return os << L',' << get<1>(n) << L',' << get<2>(n) << L" >";
}
wostream& operator<<(wostream& os, const pnode& p) {
	return isnull(p) ? os << L"(null)" : os << get<node>(p);
}
wostream& operator<<(wostream& os, const drule& d) {
	os << get<wstring>(d) << L" -> ";
	for (size_t n = 0; n < get<prod>(d).size(); ++n) {
		os << get<prod>(d)[n] << L" ";
		if (n == get<size_t>(d)) os << L"* ";
	}
	if (get<prod>(d).size() == get<size_t>(d)) os << L"*";
	return os;
}
wostream& operator<<(wostream& os, const sppf& F) {
	for (auto x : F) {
		os << x.first;
		for (auto y : x.second)
			os << L'(' << y.first << L", " << y.second << L"); ";
		os << endl;
	}
	return os;
}
////////////////////////////////////////////////////////////////////////////////
void copy(set<eitem>& l, const eset& e) {
	l.clear();
        for (auto x : e) for (auto y : x.second) l.emplace(y);
}
eitem pop(set<eitem>& s) {
	eitem r = *s.begin();
	s.erase(s.begin());
	return r;
}
////////////////////////////////////////////////////////////////////////////////
class earley {
	set<eitem> R, _Q, Q;
	set<node> V;
	map<wstring, set<pnode>> H;
	eset *E;
	cfg& P;
	sppf F;
	wstring in, S;
	size_t i = 0;
	bool nonterm(const wstring& s) const { return has(P, s); }
	void add_item(const wstring& X, eitem ei, pnode p) {
		get<pnode>(ei) = p;
		if (nonterm(X)) {
		       	if (!has(E[i][X], ei))
				E[i][X].emplace(ei), R.emplace(ei), 
				wcout<<L"add_item(E, R): "<<X<<L' '<<ei<<endl;
		}
		else if (	(i < in.size()-1 && samechar(in[i+1], X)) ||
				(i >= in.size()-1 && !X.size()))
			Q.emplace(ei),
			wcout<<L"add_item(Q): "<<X<<L' '<<ei<<endl;
	}
	node make_node(const eitem& e, pnode v, size_t k) {
		bool b = true;
		const drule& dr = rl(e);
		variant<wstring, drule> s;
		for (size_t j = get<size_t>(dr); j<get<prod>(dr).size()&&b; ++j)
			b &= !get<prod>(dr)[j].size();
		if (b) s = get<wstring>(dr);
		else {	s = dr, b = true;
			for (int j = 0; j < ((int)get<size_t>(dr)) - 1 &&b;++j)
				b &= !get<prod>(dr)[j].size();
			if (b) return (wcout<<L"returned node: " << v << endl),
					get<node>(v);
		}
		node y(s, get<size_t>(e), k);
		V.emplace(y);
		if (isnull(get<pnode>(e))) F[y].emplace(v, nullptr);
		else F[y].emplace(get<node>(get<pnode>(e)), v);
		wcout << L"made node: " << y << endl;
		return y;
	}
	void Rprocess(eitem lambda);
	void Qprocess(eitem lambda, node& v);
public:
	earley(cfg& P, const wstring& in, wstring S) : P(P), in(in), S(S) {}
	pair<const pnode&, const sppf&> operator()();
};
////////////////////////////////////////////////////////////////////////////////
void earley::Rprocess(eitem lambda) {
	wcout << L"lambda (R): " << lambda << endl;
	const drule& dr = rl(lambda);
	eitem x1, l1;
	pnode w;
	size_t h;
	if (get<size_t>(dr) < get<prod>(dr).size()) {
		const wstring& C = afterdot(rl(lambda));
		for (const prod& delta : P[C])
			add_item(C, {drule(C,delta,0),i,nullptr} , nullptr);
		for (pnode v : H[C])
			l1 = next(lambda), 
			add_item(afterdot(rl(l1)), l1 , make_node(l1, v, i));
	} else {
		const wstring& D = get<wstring>(rl(lambda));
		if (isnull(w = get<pnode>(lambda)))
			get<pnode>(lambda) = w = node(D, i, i),
			V.emplace(get<node>(w)),
			F[get<node>(w)].emplace( node({}, i, i), nullptr);
		if ((h = get<size_t>(lambda)) == i)
			H[D].emplace(w);
		for (const eitem& x : E[h][D])
			x1 = next(x),
			add_item(afterdot(rl(x1)), x1, make_node(x1, w, i));
	}
}	
void earley::Qprocess(eitem lambda, node& v) {
	drule& dr = rl(lambda);
	if (get<size_t>(dr) < get<prod>(dr).size())
		++get<size_t>(dr);
	wcout << L"lambda (Q): " << lambda << endl;
	get<pnode>(lambda) = make_node(lambda, v, i + 1);
	wstring nx(afterdot(dr));
	if (nonterm(nx) || (!nx.size() && i<in.size()))
		E[i+1][nx].emplace(lambda);
	else if (i < in.size()-2 && !nonterm(nx) &&
		get<size_t>(dr) < get<prod>(dr).size()-1 &&samechar(in[i+2],nx))
		_Q.emplace(lambda);
}
pair<const pnode&, const sppf&> earley::operator()() {
	E = new eset[in.size() + 1];
	wstring nx;
	for (const prod& alpha : P[S])
		if (nonterm(alpha[0]))
			E[0][alpha[0]].emplace(drule(S, alpha, 0), 0, nullptr);
		else if (alpha[0][0] == in[0])
			_Q.emplace(drule(S, alpha, 0), 0, nullptr);
	for (i = 0; i <= in.size(); ++i) {
		wcout<<L"E["<<i<<L']'<<endl<< E[i] << endl;
		copy(R, E[i]), Q = _Q;
		_Q.clear(), H.clear();
		while (!R.empty())
			Rprocess(pop(R));
		wcout	<<L"Q["<<i<<L']'<<endl << Q << endl << L"E["<<i<<L']'
			<< endl << E[i] << endl;
		V.clear();
		node v(format(in[i+1]), i, i + 1);
		while (!Q.empty())
			Qprocess(pop(Q), v);
		wcout<<L"E["<<i<<L']'<<endl<< E[i] << endl;
		if (i != in.size()) wcout<<L"E["<<i+1<<L']'<<endl<<E[i+1]<<endl;
	}
	drule dr;
	wcout << node();
	for (auto t : E[in.size()])
		for (eitem i : t.second)
			if (S == get<wstring>(dr = rl(i)) &&
				get<size_t>(dr) == get<prod>(dr).size())
				return { get<pnode>(i), F };
	return { nullptr, F };
}
////////////////////////////////////////////////////////////////////////////////
int main(int, char**) {
	setlocale(LC_ALL, "");
	wstring S(L"S"), T(L"T"), B(L"B"), a(L"a"), b(L"b"), ws(L"ws"), eps;
	cfg g;
	g[S].emplace(prod{ S, T });
	g[S].emplace(prod{ a });
	g[B].emplace(prod{ eps });
	g[T].emplace(prod{ a, B });
	g[T].emplace(prod{ a });

	earley &e = *new earley(g, L"aa", S);
	auto r = e();
	wcout << endl << r.second << endl;

	return 0;
}
