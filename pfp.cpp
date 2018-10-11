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
typedef array<int_t, 3> node; // [bdd] node is a triple: varid, 1-node-id, 0-node-id
typedef const wchar_t* wstr;
template<typename K> using matrix = vector<vector<K>>; // used as a set of terms (e.g. rule)
typedef vector<bool> bools;
typedef vector<bools> vbools;
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
struct rule { // a [P-DATALOG] rule in bdd form with additional information
	bool neg;
	int_t h; // bdd root
	size_t w; // nbodies, will determine the virtual power
	set<int_t> x; // existentials
	map<int_t, int_t> hvars; // how to permute body vars to head vars
};
////////////////////////////////////////////////////////////////////////////////////////////////////
class bdds_base {
	vector<node> V; // all nodes
	map<node, int_t> M; // node to its index
	int_t root; // used for implicit power
	size_t dim = 1; // used for implicit power
protected:
	int_t add(const node& n);
	int_t add_nocheck(const node& n) { return V.emplace_back(n), M[n]=V.size()-1; }
	bdds_base() { add_nocheck({{0, 0, 0}}), add_nocheck({{0, 1, 1}}); }
public:
	static const int_t F = 0, T = 1;
	node getnode(size_t n) const; // node from id. equivalent to V[n] unless virtual pow is used
	void setpow(int_t _root, size_t _dim) { root = _root, dim = _dim; }
};
////////////////////////////////////////////////////////////////////////////////////////////////////
// the following to be used with bdds::apply()
struct op_or_t { int_t operator()(int_t x, int_t y) const { return (x||y)?1:0; } } op_or; 
struct op_and_t { int_t operator()(int_t x, int_t y) const { return (x&&y)?1:0; } } op_and; 
struct op_and_not_t { int_t operator()(int_t x, int_t y) const { return (x&&!y)?1:0; } } op_and_not;
////////////////////////////////////////////////////////////////////////////////////////////////////
vbools& operator*=(vbools& x, const pair<const vbools&, size_t>& y); // to be used with allsat()

class bdds : public bdds_base { // holding functions only, therefore tbd: dont use it as an object
	int_t from_bit(int_t x, bool v) { return add(v ? node{{x+1, T, F}} : node{{x+1, F, T}}); }
	size_t count(int_t x, size_t nvars) const;
	vbools& sat(int_t x, vbools& r) const;
public:
	template<typename op_t> static // binary application
	int_t apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op);
	template<typename op_t> static int_t apply(const bdds& b, int_t x, bdds& r, const op_t& op);
	template<typename op_t> static int_t apply(bdds& b, int_t x,bdds& r, const op_t& op);//unary
	static int_t permute(bdds& b, int_t x, bdds& r, const map<int_t, int_t>&);
	// helper constructors
	int_t from_eq(int_t x, int_t y); // a bdd saying "x=y"
	template<typename K> rule from_rule(matrix<K> v, const size_t bits, const size_t ar);
	template<typename K> matrix<K> from_bits(int_t x, const size_t bits, const size_t ar);
	// helper apply() variations
	int_t bdd_or(int_t x, int_t y)	{ return apply(*this, x, *this, y, *this, op_or); } 
	int_t bdd_and(int_t x, int_t y)	{ return apply(*this, x, *this, y, *this, op_and); } 
	int_t bdd_and_not(int_t x, int_t y){ return apply(*this, x, *this, y, *this, op_and_not); }
	// count/return satisfying assignments
	size_t satcount(int_t x, size_t nvars) const;
	vbools allsat(int_t x, size_t nvars) const;
	void out(wostream& os, const node& n) const; // print a bdd, using ?: syntax
	void out(wostream& os, size_t n) const	{ out(os, getnode(n)); }
};

struct op_exists { // existential quantification, to be used with apply()
	const set<int_t>& s;
	op_exists(const set<int_t>& s) : s(s) { }
	node operator()(bdds& b, const node& n) const {
		return s.find(n[0]) == s.end() ? n : b.getnode(b.bdd_or(n[1], n[2]));
	}
};
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K> class dict_t { // handles representation of strings as unique integers
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
template<typename K> class lp { // [pfp] logic program
	dict_t<K> dict; // hold its own dict so we can determine the universe size
	bdds prog, dbs; // separate bdds for prog and db cause db is a virtual power
	vector<rule> rules; // prog's rules

	K str_read(wstr *s); // parser's helper, reads a string and returns its dict id
	vector<K> term_read(wstr *s); // read raw term (no bdd)
	matrix<K> rule_read(wstr *s); // read raw rule (no bdd)
	size_t bits, ar;
public:
	int_t db; // db's bdd root
	void prog_read(wstr s);
	void step(); // single pfp step
	void printdb(wostream& os) {
		for (const vector<K>& v : dbs.from_bits<K>(db, bits, ar)) {
			for (const K& k : v) os << k << L' ';
			os << endl;
		}
	}
};
////////////////////////////////////////////////////////////////////////////////////////////////////
int_t bdds_base::add(const node& n) { // create new bdd node, standard implementation
	if (n[1] == n[2]) return n[1];
	auto it = M.find(n);
	return it == M.end() ? add_nocheck(n) : it->second;
}

node bdds_base::getnode(size_t n) const { // returns a bdd node considering virtual powers
	if (dim == 1) return V[n];
	const size_t m = n % V.size(), ms = (n / V.size() + 1) * V.size();
	node r = V[m];
	return r[0] ? r[1] += ms, r[2] += ms, r : r[1] ? ms == V.size()*dim ? V[T] : V[root] : V[F];
}

size_t bdds::count(int_t x, size_t nvars) const {
	node n = getnode(x), k;
	size_t r = 0;
	if (!n[0]) r = n[1];
//	if (k = getnode(n[1]); !k[0]) r += k[1];
//	else r += count(n[1]) << (k[0] - n[0] - 1);
//	if (k = getnode(n[2]); !k[0]) return r + k[1];
//	else return r + (count(n[2])<<(k[0]-n[0]-1));
	else {
		k = getnode(n[1]);
		r += count(n[1], nvars) * (1 << (((k[0] ? k[0] : nvars+1) - n[0]) - 1));
		k = getnode(n[2]);
		r += count(n[2], nvars) * (1 << (((k[0] ? k[0] : nvars+1) - n[0]) - 1));
	}
	return r;
}
wostream& operator<<(wostream& os, const bools& x) {
	for (auto y : x) os << (y ? '1' : '0');
	return os;
}
wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y : x) os << y << endl;
	return os;
}
size_t bdds::satcount(int_t x, size_t nvars) const {
	if (x < 2) return x;
	return (count(x, nvars) << (getnode(x)[0] - 1));
}
vbools bdds::allsat(int_t x, size_t nvars) const {
	vbools r;
	size_t n = satcount(x, nvars);
	r.reserve(n);
	sat(x, r);
	out(wcout <<"allsat for ", x); wcout << " : " << r << endl;
	return r;
}
vbools& bdds::sat(int_t x, vbools& r) const {
	node n = getnode(x);
	node nl = getnode(n[1]), nr = getnode(n[2]);
	vbools s1, s2;
	if (nl[0]) {// || nl[1]) { // if the left node is not a leaf, or, is "true"
		s1 = r;
		for (int_t k=n[0]-1; k!=nl[0]; ++k)
			s1 *= { s1, k };
	} else if (nl[1]) s1.push_back({true});///for (bools& b : s1) b.push_back(true);// *= { {{true}}, 1 };  
	if (nr[0]) {//||nr[1]) { // if the right node is not a leaf, or, is "true"
		s2 = r;
		for (int_t k=n[0]-1; k!=nr[0]; ++k)
			s2 *= { s2, k };
	} else if (nr[1]) s2.push_back({false});//for (bools &b : s2) b.push_back(false);// *= { {{false}}, 1 };
	return r = s1 *= { s2, n[0] };
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
template<typename op_t> int_t bdds::apply(const bdds& b, int_t x, bdds& r, const op_t& op) { //unary
	node n = op(b, b.getnode(x));
	return r.add({n[0], n[1]>1?apply(b,n[1],r,op):n[1], n[2]>1?apply(b,n[2],r,op):n[2]});
}
template<typename op_t> int_t bdds::apply(bdds& b, int_t x, bdds& r, const op_t& op) { // nonconst
	node n = op(b, b.getnode(x));
	return r.add({{n[0], n[1]>1?apply(b,n[1],r,op):n[1], n[2]>1?apply(b,n[2],r,op):n[2]}});
}

int_t bdds::permute(bdds& b, int_t x, bdds& r, const map<int_t, int_t>& m) { // [overlapping] rename
	node n = b.getnode(x);
	if (!n[0]) return x;
	auto it = m.find(n[0]);
	if (it == m.end()) throw 0;
	return r.add({{it->second, n[1]>1?permute(b,n[1],r,m):n[1], n[2]>1?permute(b,n[2],r,m):n[2]}});
}

template<typename op_t> // binary application
int_t bdds::apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op) {
	const node &Vx = bx.getnode(x), &Vy = by.getnode(y);
	const int_t &vx = Vx[0], &vy = Vy[0];
	int_t v, a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) return op(a, b);
	else if ((v = vx) < vy || !vy) b = d = y;
	return r.add({{v, apply(bx, a, by, b, r, op), apply(bx, c, by, d, r, op)}});
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K> vector<K> from_bits(const bools& x, const size_t /*bits*/, const size_t ar) {
	vector<K> r;
	r.resize(ar);
	fill(r.begin(), r.end(), 0);
	for (size_t n = 0; n < x.size(); ++n) if (x[n]) r[n / ar] |= 1<<(n % ar);
	return r;
}
template<typename K> matrix<K> bdds::from_bits(int_t x, const size_t bits, const size_t ar) {
	vbools s = allsat(x, bits * ar);
	matrix<K> r;
	r.resize(s.size());
	size_t n = 0;
	for (const bools& b : s) r[n++] = ::from_bits<K>(b, bits, ar);
	return r;
}
template<typename K> rule bdds::from_rule(matrix<K> v, const size_t bits, const size_t ar) {
	int_t r = T, k;
	size_t i, j, b;
	map<K, array<size_t, 2>> m;
	set<K> ex;
	map<K, int_t> hvars; // argwise
	map<int_t, int_t> hv;// bitwise
	vector<K>& head = v[v.size()-1];
	bool neg = head[0] < 0, bneg; // negation denoted by negative relid. head is last
	if (neg) head[0] = -head[0];
	for (i = 0; i != head.size(); ++i) if (head[i] < 0) hvars.emplace(head[i], i); // head vars
	for (i = 0; i != (v.size()-1 ? v.size() - 1 : 1); ++i) { // go over bodies
		if (k = T; (bneg = (v[i][0] < 0))) v[i][0] = -v[i][0];
		for (j = 0; j != v[i].size(); ++j) // per relid/arg
			if (auto it = m.find(v[i][j]); it != m.end()) // if seen
				for (b = 0; b != bits; ++b)
					k = bdd_and(k,from_eq((i*bits+b)*ar+j,
							(it->second[0]*bits+b)*ar+it->second[1]));
			else if (m.emplace(v[i][j], array<size_t, 2>{ {i, j} }); v[i][j] > 0) // sym
				for (b = 0; b != bits; ++b)
					k = bdd_and(k, from_bit((i*bits+b)*ar+j, v[i][j]&(1<<b)));
			else if (auto jt = hvars.find(v[i][j]); jt == hvars.end()) //non-head var
				for (b = 0; b != bits; ++b)
					ex.emplace((i*bits+b)*ar+j); // is an "existential"
			else for (b=0; b != bits; ++b)
				hv.emplace((i*bits+b)*ar+j, b*ar+jt->second);
		r = bneg ? bdd_and_not(r, k) : bdd_and(r, k);
	}
	wcout << endl << "from_rule() with bits="<<bits<<" ar="<<ar<<" for ";
	for (auto x : v) { for (auto y : x) wcout << y << ' '; wcout << endl; }
	out(wcout, r); wcout << endl;
	return { neg, r, v.size()-1, ex, hv };
}

vbools& operator*=(vbools& x, const pair<const vbools&, size_t>& y) {
	size_t sx = x.size(), sy = y.first.size();
	x.reserve(sx + sy);
	for (size_t n = 0; n != sy; ++n) x.push_back(y.first[n]);
	sy += sx;
	while (sy-- != sx) x[sy][y.second] = false;
	while (sx--) x[sx][y.second] = true;
	return x;
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename K>
bool dict_t<K>::dictcmp::operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const{
	if (x.second != y.second) return x.second < y.second;
	return wcsncmp(x.first, y.first, x.second) < 0;
}

template<typename K> K dict_t<K>::operator()(wstr s, size_t len) {
	if (*s == L'?') {
		if (auto it = vars_dict.find({s, len}); it != vars_dict.end())
			return it->second;
		return vars_dict[{s, len}] = -vars_dict.size()-1;
	}
	if (auto it = syms_dict.find({s, len}); it != syms_dict.end()) return it->second;
	return syms.push_back(s), lens.push_back(len), syms_dict[{s, len}] = syms.size();
}

template<typename K> K lp<K>::str_read(wstr *s) {
	wstr t;
	while (**s && iswspace(**s)) ++*s;
	if (!**s) return 0;
	if (*(t = *s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
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
	r.push_back(b ? -rel : rel);
	if (!rel) return {};
	if (*((*s)++) != L'(') er(oparen_expected);
	do {
		while (iswspace(**s)) ++*s;
		if (**s == L')') return ++*s, r;
		if (!(t = str_read(s)))
			er("identifier expected");
		r.push_back(t);
	} while (**s);
	er("term_read(): unexpected parsing error");
}

template<typename K> matrix<K> lp<K>::rule_read(wstr *s) {
	vector<K> t;
	matrix<K> r;
	if ((t = term_read(s)).empty()) return r;
	r.push_back(t);
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	while (iswspace(**s)) ++*s;
	if (*((*s)++) != L':' || *((*s)++) != L'-') er(sep_expected);
loop:	if ((t = term_read(s)).empty()) er("term expected");
	r.insert(r.end()-1, t); // make sure head is last
	while (iswspace(**s)) ++*s;
	if (**s == L'.') return ++*s, r;
	goto loop;
}

template<typename K> void lp<K>::prog_read(wstr s) {
	vector<matrix<K>> r;
	db = bdds::F;
	size_t l;
	ar = 0;
	for (matrix<K> t; !(t = rule_read(&s)).empty(); r.push_back(t))
		for (const vector<K>& x : t) // we really support a single rel arity
			ar = max(ar, x.size()); // so we'll pad everything
	for (matrix<K>& x : r)
		for (vector<K>& y : x)
			if ((l=y.size()) < ar)
				y.resize(ar), fill(y.begin()+l, y.end(), dict.pad); // the padding
	bits = dict.bits();
	for (const matrix<K>& x : r)
	 	if (x.size() == 1) {
			db = dbs.bdd_or(db, dbs.from_rule(x, bits, ar).h);// fact
			dbs.out(wcout << endl << L"db: ", db);
		} else {
			rules.push_back(prog.from_rule(x, bits, ar)); // rule
			prog.out(wcout << endl, rules.back().h);
		}
}

template<typename K> void lp<K>::step() {
	int_t add = bdds::F, del = bdds::F, s;
	for (const rule& r : rules) { // per rule
		dbs.setpow(db, r.w);
		int_t x = bdds::apply(prog, r.h, dbs, db, prog, op_and); // rule/db conjunction
		int_t y = bdds::apply(prog, x, prog, op_exists(r.x)); // remove nonhead variables
		int_t z = bdds::permute(prog, y, prog, r.hvars); // reorder the remaining vars
		(r.neg ? del : add) = prog.bdd_or(r.neg ? del : add, z); // disjunct with add/del
	}
	if ((s = prog.bdd_and_not(add, del)) == bdds::F) db = bdds::F; // detect contradiction
	else db = prog.bdd_or(prog.bdd_and_not(bdds::T, del), s); // db = (db|add)&~del
}
////////////////////////////////////////////////////////////////////////////////////////////////////
wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n != 31; ++n)
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
	p.printdb(wcout<<endl);
	p.step();
	p.printdb(wcout<<endl);
	return 0;
}
