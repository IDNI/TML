#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include <cstdint>
#include <string>
#include <cstring>
#include <iostream>
#include <random>
#include <sstream>
#include <climits>
using namespace std;

typedef int32_t int_t;
typedef array<int_t, 3> node;
typedef const wchar_t* wstr;
template<typename K> using matrix = vector<vector<K>>;
#define er(x)	perror(x), exit(0)
#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define dot_after_q "expected '.' after query.\n"
#define if_expected "'if' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
////////////////////////////////////////////////////////////////////////////////////////////////////
struct rule {
	bool neg;
	int_t h; // bdd root
	set<int_t> x; // existentials
};
////////////////////////////////////////////////////////////////////////////////////////////////////
class bdds_base {
	vector<node> V;
	map<node, int_t> M;
	int_t root;
	size_t dim = 1;
protected:
	int_t add(const node& n);
	int_t add_nocheck(const node& n) { return V.emplace_back(n), M[n]=V.size()-1; }
	bdds_base() { add_nocheck({0, 0, 0}), add_nocheck({0, 1, 1}); }
public:
	static const int_t F = 0, T = 1;
	node getnode(size_t n) const;
	void setpow(int_t _root, size_t _dim) { root = _root, dim = _dim; }
};
////////////////////////////////////////////////////////////////////////////////////////////////////
template<bool unset> struct op_set : public set<int_t> {
	using set<int_t>::set;
	node operator()(const bdds_base& b, const node& n) const {
		return find(n[0])==end()?n:b.getnode(n[unset?2:1]);
	}
}; 
template<typename X, typename Y> struct op_compose {
	X x;
	Y y;
	op_compose(const X& x, const Y& y) : x(x), y(y) {}
	node operator()(const bdds_base& b, const node& n) const { return x(b, y(b, n)); }
}; 
struct op_set_unset : public op_compose<op_set<false>, op_set<true>> {
	op_set_unset(const set<int_t>& s, const set<int_t>& us) :
		op_compose(op_set<false>(s.begin(), s.end()), op_set<true>(us.begin(), us.end())) {}
};
struct op_or_t { int_t operator()(int_t x, int_t y) const { return (x||y)?1:0; } } op_or; 
struct op_and_t { int_t operator()(int_t x, int_t y) const { return (x&&y)?1:0; } } op_and; 
struct op_and_not_t { int_t operator()(int_t x, int_t y) const { return (x&&!y)?1:0; } } op_and_not;
////////////////////////////////////////////////////////////////////////////////////////////////////
typedef vector<bool> bits;
typedef vector<bits> vbits;
vbits& operator*=(vbits& x, const pair<const vbits&, size_t>& y);

class bdds : public bdds_base {
	template<typename op_t> static
	int_t apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op);
	template<typename op_t> static int_t apply(const bdds& b, int_t x, bdds& r, const op_t& op);
	int_t from_bit(int_t x, bool v) { return add(v ? node{x, T, F} : node{x, F, T}); }
	size_t count(int_t x) const;
public:
	int_t from_bvec(const bits& v);
	template<typename K>
	rule from_rule(const matrix<K>& v, const size_t bits, const size_t ar);
	void out(wostream& os, const node& n) const;
	void out(wostream& os, size_t n) const	{ out(os, getnode(n)); }
	int_t bdd_or(int_t x, int_t y)	{ return apply(*this, x, *this, y, *this, op_or); } 
	int_t bdd_and(int_t x, int_t y)	{ return apply(*this, x, *this, y, *this, op_and); } 
	int_t bdd_and_not(int_t x, int_t y){ return apply(*this, x, *this, y, *this, op_and_not); }
	size_t satcount(int_t x) const	{ return x < 2 ? x : (count(x) << (getnode(x)[0] - 1)); }
	vbits& sat(int_t x, vbits& r) const;
	vbits allsat(int_t x) const;
	int_t from_eq(int_t x, int_t y);
};
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K> class dict_t {
	struct dictcmp {
		bool operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const;
	};
	map<pair<wstr, size_t>, K, dictcmp> syms_dict, vars_dict;
	vector<wstr> syms;
	vector<size_t> lens;
public:
	const K pad = 1;
	dict_t() { syms.push_back(0), lens.push_back(0), syms_dict[{0, 0}] = pad; }
	K operator()(wstr s, size_t len);
	pair<wstr, size_t> operator()(K t) { return { syms[t-1], lens[t-1] }; }
	size_t bits() const { return (sizeof(K)<<3) - __builtin_clz(syms.size()); }
};
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K> class lp {
	dict_t<K> dict;
	bdds prog, _db;
	vector<rule> rules;

	K str_read(wstr *s);
	vector<K> term_read(wstr *s);
	matrix<K> rule_read(wstr *s);
public:
	void prog_read(wstr s);
	int_t step(rule r, int_t db, bdds& res);
};
////////////////////////////////////////////////////////////////////////////////////////////////////
int_t bdds_base::add(const node& n) {
	if (n[1] == n[2]) return n[1];
	auto it = M.find(n);
	return it == M.end() ? add_nocheck(n) : it->second;
}

node bdds_base::getnode(size_t n) const {
	if (dim == 1) return V[n];
	const size_t m = n % V.size(), ms = (n / V.size() + 1) * V.size();
	node r = V[m];
	if (!r[0]) {
		if (!r[1]) return V[F];
		return ms == V.size() * dim ? V[T] : V[root];
	} else return r[1] += ms, r[2] += ms, r;
}

size_t bdds::count(int_t x) const {
	node n = getnode(x);
	if (!n[0]) return n[1];
	size_t r = 0;
	if (node k = getnode(n[1]); !k[0]) r += k[1];
	else r += count(n[1]) << (k[0] - n[0] - 1);
	if (node k = getnode(n[2]); !k[0]) r += k[1];
	else r += count(n[2]) << (k[0] - n[0] - 1);
	return r;
}

int_t bdds::from_bvec(const bits& v) {
	int_t k = T, n = v.size() - 1;
	do { k = v[n] ? add({n+1, k, F}) : add({n+1, F, k}); } while (n--);
	return k;
}

vbits& bdds::sat(int_t x, vbits& r) const {
	node n = getnode(x);
	node nl = getnode(n[1]), nr = getnode(n[2]);
	vbits s1, s2;
	if (nl[0]||nl[1]) { s1=r; for (int_t k=n[0]-1; k!=nl[0]; ++k) s1 *= { s1, k }; }
	if (nr[0]||nr[1]) { s2=r; for (int_t k=n[0]-1; k!=nr[0]; ++k) s2 *= { s2, k }; }
	return r = s1 *= { s2, n[0] };
}

vbits bdds::allsat(int_t x) const {
	vbits r;
	r.reserve(satcount(x));
	return sat(x, r);
}

int_t bdds::from_eq(int_t x, int_t y) {
	return bdd_or(	bdd_and(from_bit(x, true), from_bit(y, true)),
			bdd_and(from_bit(x, false),from_bit(y, false)));
}

void bdds::out(wostream& os, const node& n) const {
	if (!n[0]) os << (n[1] ? L'T' : L'F');
	else out(os << n[0] << L'?', getnode(n[1])), out(os << L':', getnode(n[2]));
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename op_t> int_t bdds::apply(const bdds& b, int_t x, bdds& r, const op_t& op) {
	node n = op(b, b.getnode(x));
	return r.add({n[0], n[1]>1?apply(b,n[1],r,op):n[1], n[2]>1?apply(b,n[2],r,op):n[2]});
}

template<typename op_t>
int_t bdds::apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op) {
	const node &Vx = bx.getnode(x), &Vy = by.getnode(y);
	const int_t &vx = Vx[0], &vy = Vy[0];
	int_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) return op(a, b);
	else if ((v = vx) < vy || !vy) b = d = y;
	return r.add({v, apply(bx, a, by, b, r, op), apply(bx, c, by, d, r, op)});
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K>
rule bdds::from_rule(const matrix<K>& v, const size_t bits, const size_t ar) {
	int_t r = T;
	map<K, array<size_t, 2>> m;
	set<K> hvars, ex;
	for (K k : v[0]) if (k < 0) hvars.emplace(k);
	for (size_t i = 1; i < v.size(); ++i) {
		int_t k = T;
		for (size_t j = 1; j < v[i].size(); ++j)
			if (auto it = m.find(v[i][j]); it != m.end())
				for (size_t b = 0; b != bits; ++b)
					k = bdd_and(k,from_eq((i*bits+b)*ar+j,
							(it->second[0]*bits+b)*ar+it->second[0]));
			else if (m.emplace(v[i][j], array<size_t, 2>{ i, j }); v[i][j] > 0)
				for (size_t b = 0; b != bits; ++b)
					k = bdd_and(k, from_bit((i*bits+b)*ar+j, v[i][j]&(1<<b)));
			else if (hvars.find(v[i][j]) == hvars.end())
				for (size_t b = 0; b != bits; ++b)
					ex.emplace((i*bits+b)*ar+j);
		r = v[i][0] > 0 ? bdd_and(r, k) : bdd_and_not(r, k);
	}
	return { v[0][0] > 0, r, ex };
}

vbits& operator*=(vbits& x, const pair<const vbits&, size_t>& y) {
	size_t sx = x.size(), sy = y.first.size();
	x.reserve(sx + sy);
	for (size_t n = 0; n < sy; ++n) x.push_back(y.first[n]);
	sy += sx;
	while (sy-- != sx) x[sy][y.second] = false;
	while (sx--) x[sx][y.second] = true;
	return x;
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K>
bool dict_t<K>::dictcmp::operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const {
	if (x.second != y.second) return x.second < y.second;
	return wcsncmp(x.first, y.first, x.second) < 0;
}

template<typename K> K dict_t<K>::operator()(wstr s, size_t len) {
	if (*s == L'?') {
		if (auto it = vars_dict.find({s, len}); it != vars_dict.end())
			return it->second;
		return vars_dict[{s, len}] = -vars_dict.size();
	}
	if (auto it = syms_dict.find({s, len}); it != syms_dict.end()) return it->second;
	return syms.push_back(s), lens.push_back(len), syms.size();
}

template<typename K> K lp<K>::str_read(wstr *s) {
	wstr t;
	while (**s && iswspace(**s)) ++*s;
	if (!**s) return 0;
	if (*(t = *s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	while (iswspace(*t)) ++t;
	if (t == *s) return 0;
	K r = dict(*s, t - *s);
	while (*t && iswspace(*t)) ++t;
	return *s = t, r;
}

template<typename K> vector<K> lp<K>::term_read(wstr *s) {
	vector<K> r;
	while (iswspace(**s)) ++*s;
	bool b = **s == L'~';
	if (b) ++*s;
	K rel = str_read(s), t;
	r.push_back(b ? rel : -rel);
	if (!rel) return {};
	if (*((*s)++) != L'(') er(oparen_expected);
	do {
		while (iswspace(**s)) ++*s;
		if (**s == L')') return r;
		if (!(t = str_read(s))) er("identifier expected");
		r.push_back(t);
	} while (**s);
	er("term_read(): unexpected parsing error");
}

template<typename K> matrix<K> lp<K>::rule_read(wstr *s) {
	vector<K> t;
	matrix<K> r;
	if ((t = term_read(s)).empty()) return r;
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return r;
	if (*((*s)++) != L':' || *((*s)++) != L'-') er(sep_expected);
loop:	if ((t = term_read(s)).empty()) er("term expected");
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return r;
	goto loop;
}

template<typename K> void lp<K>::prog_read(wstr s) {
	vector<matrix<K>> r;
	matrix<K> t;
	int_t db = bdds::T;
	size_t ar = 0, l, dim = 0;
	while (!(t = rule_read(&s)).empty()) {
		dim = max(t.size()-1, dim);
		for (const vector<K>& x : t) ar = max(ar, x.size());
		r.push_back(t);
	}
	for (matrix<K>& x : r)
		for (vector<K>& y : x)
			if ((l=y.size()) < ar)
				y.resize(ar), fill(y.begin()+l, y.end(), dict.pad);
	for (const matrix<K>& x : r)
		if (x.size() == 1) db = _db.bdd_or(db, _db.from_rule(x, dict.bits(), ar).h);
		else rules.push_back(prog.from_rule(x, dict.bits(), ar));
	_db.setpow(db, dim);
}

template<typename K> int_t lp<K>::step(rule r, int_t db, bdds& res) {
	int_t s = bdds::apply(prog, r.h, _db, db, res, op_and);
	//s = res.bdd_ex(s, r.ex); 
}
////////////////////////////////////////////////////////////////////////////////////////////////////
wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n < 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = 0; break; }
		else if (c == L'#') skip = 1;
		else if (c == L'\r' || c == L'\n') skip = 0, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0, ss << buf;
		goto next;
	} else if (skip) goto next;
	return ss.str();
}
////////////////////////////////////////////////////////////////////////////////////////////////////
int main() {
	setlocale(LC_ALL, "");
	lp<int32_t> p;
	p.prog_read(file_read_text(stdin).c_str());
//	return pfp( lp_read(file_read_text(stdin).c_str()));
}
