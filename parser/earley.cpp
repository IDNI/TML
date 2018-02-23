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
wstring afterdot(const drule& d) {
	const prod& p = get<prod>(d);
	return get<size_t>(d) >= p.size() ? wstring() : p[get<size_t>(d)];
}

eitem next(const eitem& e) {
	eitem r(e);
	return ++get<size_t>(get<drule>(r)), r;
}

template<typename C, typename V> bool has(const C& x, const V& y) {
	return x.find(y) != x.end();
}

bool samechar(wchar_t c, const wstring& s) {
	if (!s.size()) return !c;
	if (s == L"ws") return iswspace(c);
	if (s == L"alnum") return iswalnum(c);
	if (s == L"cr") return c == L'\r';
	if (s == L"lf") return c == L'\n';
	if (s.size() > 1) return false;
	return s[0] == c;
}

bool nonterm(const cfg& g, const drule& d) { return has(g, afterdot(d)); }
////////////////////////////////////////////////////////////////////////////////
wostream& print(wostream& os, const wstring& s) { os << s; return os; }

wostream& print(wostream& os, const drule& d) {
	os << get<wstring>(d) << L" -> ";
	size_t n = 0;
	for (; n < get<size_t>(d); ++n) print(os, get<prod>(d)[n]) << L' ';
	os << L"* ";
	while (n < get<prod>(d).size()) print(os, get<prod>(d)[n++]) << L' ';
	return os;
}

wostream& print(wostream& os, const node& n) {
	if (holds_alternative<wstring>(get<0>(n)))
		print(os, get<wstring>(get<0>(n))) << L' ' << get<1>(n) << L' ' << get<2>(n);
	else print(os, get<drule>(get<0>(n))) << L' ' << get<1>(n) << L' ' << get<2>(n);
	return os;
}

wostream& print(wostream& os, const pnode& p) {
	if (holds_alternative<nullptr_t>(p)) return os << L"(null)";
	return print(os, get<node>(p));
}

wostream& print(wostream& os, const eitem& e) {
	print(os, get<drule>(e)) << L' ' << get<size_t>(e) << L' '; 
	return print(os, get<pnode>(e));
}

wostream& print(wostream& os, const eset& e) {
	for (auto x : e) for (auto y : x.second) print(os << L'[', y) << L']' << endl;
	return os;
}

wostream& print(wostream& os, const sppf& F) {
	for (auto x : F) {
		print(os, x.first);
	       	for (auto y : x.second) {
			os << L'(';
			print(os, y.first) << L',';
			print(os, y.second) << L");";
		}
	       os << endl;
	}
	return os;
}
////////////////////////////////////////////////////////////////////////////////
void copy(set<eitem>& l, eset& e) {
	l.clear();
        for (auto x : e)
                for (auto y : x.second)
                        l.insert(y);
}
eitem pop(set<eitem>& s) {
	eitem r = *s.begin();
//	wcout << L"popped: "; print(wcout, r) << L" left on container: " << s.size() << endl;
	s.erase(s.begin());
	return r;
}

node make_node(const eitem& e, size_t i, pnode v, set<node>& V, sppf& F) {
	bool b = true;
	const drule& dr = get<drule>(e);
	variant<wstring, drule> s;
	for (size_t j = get<size_t>(dr); j < get<prod>(dr).size() && b; ++j)
		b &= !get<prod>(dr)[j].size();
	if (b) s = get<wstring>(dr);
	else {	s = dr, b = true;
		for (int j = 0; j < ((int)get<size_t>(dr)) - 1 && b; ++j)
			b &= !get<prod>(dr)[j].size();
		if (b) return wcout<<L"returned node: ", print(wcout, v) << endl, get<node>(v);
	}
	node y(s, get<size_t>(e), i);
	V.emplace(y);
	if (holds_alternative<nullptr_t>(get<pnode>(e))) F[y].emplace(v, nullptr);
	else F[y].emplace(get<node>(get<pnode>(e)), v);
	wcout<<L"made node: "; print(wcout, y) << endl;
	return y;
}

class earley {
	set<eitem> R, _Q, Q;
	set<node> V;
	eset *E;
	cfg& P;
	wstring in, S;
	size_t i = 0;
	void add_item(const wstring& X, eitem ei, pnode p) {
		get<pnode>(ei) = p;
		if (has(P, X) && !has(E[i], X))
			E[i][X].emplace(ei), R.insert(ei);
		if (samechar(in[i+1], X))
			Q.insert(ei);
		wcout << L"add_item: " << X << L' '; print(wcout, ei), print(wcout, p) << endl;
	}
public:
	earley(cfg& P, const wstring& in, wstring S) : P(P), in(in), S(S) {}
	pnode operator()(sppf& F);
};

pnode earley::operator()(sppf& F) {
	E = new eset[in.size() + 1];
	eitem x1, l1;
	pnode w;
	wstring nx;
	size_t h;
	for (const prod& alpha : P[S])
		if (has(P, alpha[0]))
			E[0][alpha[0]].emplace(drule(S, alpha, 0), 0, nullptr);
		else if (alpha[0][0] == in[0])
			_Q.emplace(drule(S, alpha, 0), 0, nullptr);
	for (i = 0; i <= in.size(); ++i) {
		copy(R, E[i]), Q = _Q;
		map<wstring, set<pnode>> H;
		_Q.clear();
		while (!R.empty()) {
			eitem lambda = pop(R);
			wcout << L"lambda (R): "; print(wcout, lambda) << endl;
			const drule& dr = get<drule>(lambda);
			if (get<size_t>(dr) < get<prod>(dr).size()) {
				const wstring& C = afterdot(get<drule>(lambda));
				for (const prod& delta : P[C])
					add_item(delta[0], { drule(C, delta, 0), i, nullptr }, nullptr);
				for (pnode v : H[C])
					l1 = next(lambda), nx = afterdot(get<drule>(l1)), 
					add_item(nx, l1, make_node(l1, i, v, V, F));
			} else {
				const wstring& D = get<wstring>(get<drule>((lambda)));
				if (holds_alternative<nullptr_t>(w = get<pnode>(lambda)))
					w = node(D, i, i), V.emplace(get<node>(w)),
					get<pnode>(lambda) = w,
					F[get<node>(w)].emplace(node(wstring(), i, i), nullptr);
				if ((h = get<size_t>(lambda)) == i)
					H[D].emplace(w);
				for (const eitem& x : E[h][D])
					x1 = next(x),
					add_item(get<prod>(get<drule>(x1))[0], x1, make_node(x1, i, w, V, F));
			}
		}
		V.clear();
		node v(wstring(1, in[i + 1]), i, i + 1);
		while (!Q.empty()) {
			eitem lambda = pop(Q);
			drule& dr = get<drule>(lambda);
//				assert(get<size_t>(dr) == get<prod>(dr).size());
//			else {
			++get<size_t>(dr);
			assert(samechar(in[i+1], get<prod>(dr)[get<size_t>(dr) - 1]));
			wcout << L"lambda (Q): "; print(wcout, lambda) << endl;
			get<pnode>(lambda) = make_node(lambda, i + 1, v, V, F);
			wstring nx(afterdot(dr));
			if (get<size_t>(dr) < get<prod>(dr).size() - 1) {
				if (has(P, nx))
					E[i+1][nx].emplace(lambda);
				else if (samechar(in[i+2], nx))
					_Q.insert(lambda);
			}
		}
		print(wcout<<L"E["<<i<<L']'<<endl, E[i]);
	}
	drule dr;
	for (auto t : E[in.size()])
		for (eitem i : t.second)
			if (S == get<wstring>(dr = get<drule>(i)) &&
				get<size_t>(dr) == get<prod>(dr).size())
				return get<pnode>(i);
	return nullptr;
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

	sppf F;
	earley &e = *new earley(g, L"aa", S);
	print(wcout, e(F));
	print(wcout, F);

	return 0;
}
