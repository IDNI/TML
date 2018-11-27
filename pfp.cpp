#include <set>
#include <map>
#include <vector>
#include <string>
#include <cstring>
#include <iostream>
#include <sstream>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
using namespace std;

typedef long int_t;
struct node {
	int_t var, hi, lo;
	node(int_t var, int_t hi, int_t lo) : var(var), hi(hi), lo(lo) {}
	bool operator<(const node& n) const {
		return var!=n.var ? var<n.var : hi!=n.hi ? hi<n.hi : lo!=n.lo ? lo<n.lo : false; }
};
typedef const wchar_t* wstr;
////////////////////////////////////////////////////////////////////////////////////////////////////
struct rule { // a [P-DATALOG] rule in bdd form with additional information
	bool neg;
	int_t h, hsym; // bdd root and head syms
	size_t w; // nbodies, will determine the virtual power
	set<int_t> x; // existentials
	map<int_t, int_t> hvars; // how to permute body vars to head vars
};
////////////////////////////////////////////////////////////////////////////////////////////////////
class bdds_base {
	vector<node> V; // all nodes
	map<node, int_t> M; // node to its index
	int_t root; // used for implicit power
	size_t dim; // used for implicit power
protected:
	int_t add_nocheck(const node& n) {
		V.push_back(n);
		int_t r = (M[n]=V.size()-1);
		return r;
	}
	bdds_base() : dim(1) { add_nocheck(node(0, 0, 0)), add_nocheck(node(0, 1, 1)); }
public:
	static const int_t F = 0, T = 1;
	node getnode(size_t n) const; // node from id. equivalent to V[n] unless virtual pow is used
	void setpow(int_t _root, size_t _dim) { root = _root, dim = _dim; }
	static bool leaf(int_t x) { return x == T || x == F; }
	static bool leaf(const node& x) { return !x.var; }
	static bool trueleaf(const node& x) { return leaf(x) && x.hi; }
	wostream& out(wostream& os, const node& n) const; // print a bdd, using ?: syntax
	wostream& out(wostream& os, size_t n) const	{ return out(os, getnode(n)); }
	int_t add(const node& n);
};
////////////////////////////////////////////////////////////////////////////////////////////////////
// the following to be used with bdds::apply()
struct op_or_t { int_t operator()(int_t x, int_t y) const { return (x||y)?bdds_base::T:bdds_base::F; } } op_or; 
struct op_and_t { int_t operator()(int_t x, int_t y) const { return (x&&y)?bdds_base::T:bdds_base::F; } } op_and; 
struct op_and_not_t { int_t operator()(int_t x, int_t y) const { return (x&&!y)?bdds_base::T:bdds_base::F; } } op_and_not;
////////////////////////////////////////////////////////////////////////////////////////////////////
class bdds : public bdds_base { // holding functions only, therefore tbd: dont use it as an object
	size_t count(int_t x, size_t nvars) const;
	void sat(int_t v, int_t nvars, node n, vector<bool>& p, vector<vector<bool> >& r) const;
public:
	int_t from_bit(int_t x, bool v) { return add(v ? node(x+1, T, F) : node(x+1, F, T)); }
	template<typename op_t> static // binary application
	int_t apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op);
	template<typename op_t> static int_t apply(const bdds& b, int_t x, bdds& r, const op_t& op);
	template<typename op_t> static int_t apply(bdds& b, int_t x,bdds& r, const op_t& op);//unary
	static int_t permute(bdds& b, int_t x, bdds& r, const map<int_t, int_t>&);
	// helper constructors
	int_t from_eq(int_t x, int_t y); // a bdd saying "x=y"
	rule from_rule(vector<vector<int_t> > v, const size_t bits, const size_t ar);
	vector<vector<int_t> > from_bits(int_t x, const size_t bits, const size_t ar);
	// helper apply() variations
	int_t bdd_or(int_t x, int_t y)	{ return apply(*this, x, *this, y, *this, op_or); } 
	int_t bdd_and(int_t x, int_t y)	{ return apply(*this, x, *this, y, *this, op_and); } 
	int_t bdd_and_not(int_t x, int_t y){ return apply(*this, x, *this, y, *this, op_and_not); }
	// count/return satisfying assignments
	size_t satcount(int_t x, size_t nvars) const;
	vector<vector<bool> > allsat(int_t x, size_t nvars) const;
	using bdds_base::add;
	using bdds_base::out;
};

struct op_exists { // existential quantification, to be used with apply()
	const set<int_t>& s;
	op_exists(const set<int_t>& s) : s(s) { }
	node operator()(bdds& b, const node& n) const {
		return s.find(n.var) == s.end() ? n : b.getnode(b.bdd_or(n.hi, n.lo));
	}
};
////////////////////////////////////////////////////////////////////////////////////////////////////
class dict_t { // handles representation of strings as unique integers
	struct dictcmp {
		bool operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const;
	};
	map<pair<wstr, size_t>, int_t, dictcmp> syms_dict, vars_dict;
	vector<wstr> syms;
	vector<size_t> lens;
public:
	const int_t pad;
	dict_t() : pad(0) { syms.push_back(0), lens.push_back(0), syms_dict[make_pair<wstr, size_t>(0, 0)] = pad; }
	int_t operator()(wstr s, size_t len);
	pair<wstr, size_t> operator()(int_t t) const { return make_pair(syms[t], lens[t]); }
	size_t bits() const { return (sizeof(int_t)<<3) - __builtin_clz(syms.size()); }
	size_t nsyms() const { return syms.size(); }
};
wostream& operator<<(wostream& os, const pair<wstr, size_t>& p) {
	for (size_t n = 0; n < p.second; ++n) os << p.first[n];
	return os;
}

wostream& out(wostream& os, bdds& b, int_t db, size_t bits, size_t ar, const class dict_t& d);
////////////////////////////////////////////////////////////////////////////////////////////////////
class lp { // [pfp] logic program
	dict_t dict; // hold its own dict so we can determine the universe size
	bdds prog, dbs; // separate bdds for prog and db cause db is a virtual power
	vector<rule> rules; // prog's rules

	int_t str_read(wstr *s); // parser's helper, reads a string and returns its dict id
	vector<int_t> term_read(wstr *s); // read raw term (no bdd)
	vector<vector<int_t> > rule_read(wstr *s); // read raw rule (no bdd)
	size_t bits, ar;
public:
	int_t db; // db's bdd root
	void prog_read(wstr s);
	void step(); // single pfp step
	bool pfp();
	void printdb(wostream& os) { out(os, dbs, db, bits, ar, dict); }
};
////////////////////////////////////////////////////////////////////////////////////////////////////
wostream& operator<<(wostream& os, const vector<bool>& x){
	for (size_t n = 0; n != x.size(); ++n) os << (x[n]?0:1);
	return os;
}
wostream& operator<<(wostream& os,const vector<vector<bool> >&x){
	for (size_t n = 0; n != x.size(); ++n) os << x[n];
	return os;
}
wostream& out(wostream& os, bdds& b, int_t db, size_t bits, size_t ar, const dict_t& d) {
	vector<vector<int_t> > t = b.from_bits(db, bits, ar);
	for (size_t n = 0; n < t.size(); ++n) {
		for (size_t k = 0; k < t[n].size(); ++k)
			if (t[n][k] < (int_t)d.nsyms()) os << d(t[n][k]) << L' ';
			else os << L'[' << t[n][k] << L"] ";
		os << endl;
	}
	return os;
}

int_t bdds_base::add(const node& n) { // create new bdd node, standard implementation
	if (n.hi == n.lo) return n.hi;
	map<node, int_t>::const_iterator it = M.find(n);
	return it == M.end() ? add_nocheck(n) : it->second;
}

node bdds_base::getnode(size_t n) const { // returns a bdd node considering virtual powers
	if (dim == 1) return V[n];
	const size_t m = n % V.size(), ms = (n / V.size() + 1) * V.size();
	node r = V[m];
	return r.var ? r.hi += ms, r.lo += ms, r : r.hi ? ms == V.size()*dim ? V[T] : V[root] : V[F];
}

size_t bdds::count(int_t x, size_t nvars) const {
	node n = getnode(x);
	size_t r = 0;
	if (leaf(n)) return trueleaf(n) ? 1 : 0;
	node k = getnode(n.hi);
	r += count(n.hi, nvars) * (1 << (((leaf(k) ? nvars+1 : k.var) - n.var) - 1));
	k = getnode(n.lo);
	return r+count(n.lo, nvars)*(1<<(((leaf(k) ? nvars+1 : k.var) - n.var) - 1));
}

size_t bdds::satcount(int_t x,size_t nvars) const {
	return x<2?x?(1<<nvars):0:(count(x, nvars)<<(getnode(x).var-1));
}

void bdds::sat(int_t v, int_t nvars, node n, vector<bool>& p, vector<vector<bool> >& r) const {
	if (leaf(n) && !trueleaf(n)) return;
	if (v<n.var) p[v-1] = true, sat(v+1, nvars, n, p, r), p[v-1]=false, sat(v+1, nvars, n, p, r);
	else if (v == nvars+1) r.push_back(p);
	else p[v-1]=true, sat(v+1,nvars,getnode(n.hi),p,r), p[v-1]=false, sat(v+1,nvars,getnode(n.lo),p,r);
}

vector<vector<bool> > bdds::allsat(int_t x, size_t nvars) const {
	vector<bool> p;
	p.resize(nvars);
	vector<vector<bool> > r;
	size_t n = satcount(x, nvars);
	r.reserve(n);
	node t = getnode(x);
	sat(1, nvars, t, p, r);
	out(wcout<<"satcount: " << n <<" allsat for ", x);
	wcout << r << endl << endl;
	return r;
}

int_t bdds::from_eq(int_t x, int_t y) {
	return bdd_or(	bdd_and(from_bit(x, true), from_bit(y, true)),
			bdd_and(from_bit(x, false),from_bit(y, false)));
}

wostream& bdds_base::out(wostream& os, const node& n) const {
	if (leaf(n)) return os << (trueleaf(n) ? L'T' : L'F');
	else return out(os << n.var << L'?', getnode(n.hi)), out(os << L':', getnode(n.lo));
}
////////////////////////////////////////////////////////////////////////////////////////////////////
template<typename op_t> int_t bdds::apply(const bdds& b, int_t x, bdds& r, const op_t& op) { //unary
	node n = op(b, b.getnode(x));
	return r.add(node(n.var, leaf(n.hi)?n.hi:apply(b,n.hi,r,op), leaf(n.lo)?n.lo:apply(b,n.lo,r,op)));
}

template<typename op_t> int_t bdds::apply(bdds& b, int_t x, bdds& r, const op_t& op) { // nonconst
	node n = op(b, b.getnode(x));
	return r.add(node(n.var, leaf(n.hi)?n.hi:apply(b,n.hi,r,op), leaf(n.lo)?n.lo:apply(b,n.lo,r,op)));
}
// [overlapping] rename
int_t bdds::permute(bdds& b, int_t x, bdds& r, const map<int_t, int_t>& m) {
	node n = b.getnode(x);
	if (leaf(n)) return x;
	map<int_t, int_t>::const_iterator it = m.find(n.var);
	if (it != m.end())
		return 	r.add(node(it->second, leaf(n.hi)?n.hi:permute(b,n.hi,r,m),
			leaf(n.lo)?n.lo:permute(b,n.lo,r,m)));
//	else if (auto jt = s.find(n.var); jt == s.end())
		return r.add(node(n.var, permute(b,n.hi,r,m), permute(b,n.lo,r,m)));
//	else if (jt->second) return permute(b,n.hi,r,m,s);
//	else return permute(b,n.lo,r,m,s);
}

template<typename op_t> // binary application
int_t bdds::apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op) {
	const node &Vx = bx.getnode(x), &Vy = by.getnode(y);
	const int_t &vx = Vx.var, &vy = Vy.var;
	int_t v, a = Vx.hi, b = Vy.hi, c = Vx.lo, d = Vy.lo;
	if ((!vx && vy) || (vy && (vx > vy))) a = c = x, v = vy;
	else if (!vx) return op(a, b);
	else if ((v = vx) < vy || !vy) b = d = y;
	return r.add(node(v, apply(bx, a, by, b, r, op), apply(bx, c, by, d, r, op)));
}
////////////////////////////////////////////////////////////////////////////////////////////////////
vector<int_t> from_bits(const vector<bool>& x, const size_t ar) {
	vector<int_t> r(ar, 0);
	for (size_t n = 0; n < x.size(); ++n) if (x[n]) r[n % ar] |= 1<<(n / ar);
	return r;
}
vector<vector<int_t> > bdds::from_bits(int_t x, const size_t bits, const size_t ar) {
	vector<vector<bool> > s = allsat(x, bits * ar);
	vector<vector<int_t> > r(s.size());
	size_t n = 0;
	for (size_t k = 0; k != s.size(); ++k)
		r[n++] = ::from_bits(s[k], ar);
	return r;
}
struct sz2 { size_t x, y; sz2() {} sz2(size_t x, size_t y) : x(x), y(y) {} bool operator<(const sz2& t) { return x!=t.x?x<t.x:y!=t.y?y<t.y:false;} };
rule bdds::from_rule(vector<vector<int_t> > v, const size_t bits, const size_t ar) {
	int_t k;
	size_t i, j, b;
	map<int_t, int_t> hvars;
	vector<int_t>& head = v[v.size()-1];
	bool bneg;
	rule r;
	r.h = r.hsym = T;
	r.neg = head[0] < 0;
	head.erase(head.begin());
	r.w = v.size() - 1;
	for (i = 0; i != head.size(); ++i)
		if (head[i] < 0) hvars[head[i]] = i; // var
		else for (b = 0; b != bits; ++b) r.hsym = bdd_and(r.hsym, from_bit(b*ar+i, head[i]&(1<<b)));
		//	r.eq.emplace(b*ar+i, head[i]&(1<<b)); // sym
	#define BIT(term,arg) (term*bits+b)*ar+arg
	map<int_t, sz2> m;
	if (v.size()==1) r.h = r.hsym; // for (auto x : r.eq) r.h = bdd_and(r.h, from_bit(x.first, x.second)); //fact
	else for (i = 0; i != v.size()-1; ++i, r.h = bneg ? bdd_and_not(r.h, k) : bdd_and(r.h, k))
		for (k=T, bneg = (v[i][0]<0), v[i].erase(v[i].begin()), j=0; j != v[i].size(); ++j) {
			map<int_t, sz2>::const_iterator it = m.find(v[i][j]);
			if (it != m.end()) { // if seen
				for (b=0; b!=bits; ++b)	k = bdd_and(k,from_eq(BIT(i,j),
								BIT(it->second.x, it->second.y)));
				continue;
			}
			// auto p = make_pair<const size_t, const size_t>(i,j);
			m[v[i][j]] = sz2(i, j);
			if (v[i][j] >= 0) { // sym
				for (b=0; b!=bits; ++b)	k = bdd_and(k, from_bit(BIT(i,j),
								v[i][j]&(1<<b))), r.x.insert(BIT(i,j));
				continue;
			}
			map<int_t, int_t>::const_iterator jt = hvars.find((int_t)v[i][j]);
			if (jt == hvars.end()) //non-head var
				for (b=0; b!=bits; ++b)	r.x.insert(BIT(i,j));
			else	for (b=0; b!=bits; ++b)	r.hvars.insert(make_pair(BIT(i,j), //jt->first&(1<<b));//
				b*ar+jt->second));
		}
	#undef BIT
	out(wcout<<"from_rule: ", r.h)<<endl;
	return r;
}
////////////////////////////////////////////////////////////////////////////////////////////////////
#define er(x)	throw runtime_error(x) //perror(x), exit(0)
#define oparen_expected "'(' expected\n"
#define comma_expected "',' or ')' expected\n"
#define dot_after_q "expected '.' after query.\n"
#define if_expected "'if' or '.' expected\n"
#define sep_expected "Term or ':-' or '.' expected\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"


bool dict_t::dictcmp::operator()(const pair<wstr, size_t>& x, const pair<wstr, size_t>& y) const{
	if (x.second != y.second) return x.second < y.second;
	return wcsncmp(x.first, y.first, x.second) < 0;
}

int_t dict_t::operator()(wstr s, size_t len) {
	if (*s == L'?') {
		typename map<pair<wstr, size_t>, int_t, dictcmp>::const_iterator it = vars_dict.find(make_pair(s, len));
		return it != vars_dict.end() ? it->second : (vars_dict[make_pair(s, len)]=-vars_dict.size());
	}
	typename map<pair<wstr, size_t>, int_t, dictcmp>::const_iterator it = syms_dict.find(make_pair(s, len));
	return it==syms_dict.end()?syms.push_back(s),lens.push_back(len),syms_dict[make_pair(s,len)]=syms.size()-1:it->second;
}

int_t lp::str_read(wstr *s) {
	wstr t;
	while (**s && iswspace(**s)) ++*s;
	if (!**s) er("identifier expected");
	if (*(t = *s) == L'?') ++t;
	while (iswalnum(*t)) ++t;
	if (t == *s) er("identifier expected");
	int_t r = dict(*s, t - *s);
	while (*t && iswspace(*t)) ++t;
	return *s = t, r;
}

vector<int_t> lp::term_read(wstr *s) {
	vector<int_t> r;
	while (iswspace(**s)) ++*s;
	if (!**s) return r;
	bool b = **s == L'~';
	if (b) ++*s, r.push_back(-1); else r.push_back(1);
	do {
		while (iswspace(**s)) ++*s;
		if (**s == L',') return ++*s, r;
		if (**s == L'.' || **s == L':') return r;
		r.push_back(str_read(s));
	} while (**s);
	er("term_read(): unexpected parsing error");
}

vector<vector<int_t> > lp::rule_read(wstr *s) {
	vector<int_t> t;
	vector<vector<int_t> > r;
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

void lp::prog_read(wstr s) {
	vector<vector<vector<int_t> > > r;
	db = bdds::F;
	size_t l;
	ar = 0;
	for (vector<vector<int_t> > t; !(t = rule_read(&s)).empty(); r.push_back(t))
		for (size_t n = 0; n != t.size(); ++n)
		//for (const vector<int_t>& x : t) // we really support a single rel arity
			ar = max(ar, t[n].size()-1); // so we'll pad everything
	for (size_t n = 0; n != r.size(); ++n)
		for (size_t k = 0; k != r[n].size(); ++k)
//	for (vector<vector<int_t> >& x : r)
//		for (vector<int_t>& y : x)
			if ((l=r[n][k].size()) < ar)
				r[n][k].resize(ar), fill(r[n][k].begin()+l, r[n][k].end(), dict.pad); // the padding
	bits = dict.bits();
	for (size_t n = 0; n != r.size(); ++n)
	//for (const vector<vector<int_t> >& x : r)
	 	if (r[n].size() == 1) db = dbs.bdd_or(db, dbs.from_rule(r[n], bits, ar).h);// fact
		else rules.push_back(prog.from_rule(r[n], bits, ar)); // rule
}

void lp::step() {
	int_t add = bdds::F, del = bdds::F, s, x, y, z;
	wcout << endl;
	for (size_t n = 0; n != rules.size(); ++n) {
//	for (const rule& r : rules) { // per rule
		dbs.setpow(db, rules[n].w);
//		dbs.out<int_t>(wcout<<"db: ", db, bits, ar)<<endl;
		out(wcout<<endl<<"rule: ", prog, rules[n].h, bits, ar, dict)<<endl;
		x = bdds::apply(dbs, db, prog, rules[n].h, prog, op_and); // rule/db conjunction
//		prog.out(wcout<<"x: ", x)<<endl;
		out(wcout<<"x: ", prog, x, bits, ar, dict)<<endl;
		y = bdds::apply(prog, x, prog, op_exists(rules[n].x)); // remove nonhead variables
		out(wcout<<"y: ", prog, y, bits, ar, dict)<<endl;
		z = bdds::permute(prog, y, prog, rules[n].hvars); // reorder the remaining vars
		out(wcout<<"z: ", prog, z, bits, ar, dict)<<endl;
		out(wcout<<"hsym: ", prog, rules[n].hsym, bits, ar, dict)<<endl;
		z = prog.bdd_and(z, rules[n].hsym);
		out(wcout<<"z&hsym: ", prog, z, bits, ar, dict)<<endl;
		(rules[n].neg ? del : add) = bdds::apply(dbs, rules[n].neg ? del : add, prog, z, dbs, op_or);
	}
	dbs.out(wcout<<"db: ", db)<<endl;
	dbs.out(wcout<<"add: ", add)<<endl;
	dbs.out(wcout<<"del: ", del)<<endl;
	if ((s = dbs.bdd_and_not(add, del)) == bdds::F) db = bdds::F; // detect contradiction
	else db = dbs.bdd_or(dbs.bdd_and_not(db, del), s);// db = (db|add)&~del = db&~del | add&~del
	dbs.out(wcout<<"db: ", db)<<endl;
}

bool lp::pfp() {
	int_t d, t = 0;
	for (set<int_t> s;;) {
		s.insert(d = db);
		printdb(wcout<<"step: " << ++t << endl);
		step();
		if (s.find(db) != s.end()) return d == db;
	}
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
	lp p;
	wstring s = file_read_text(stdin); // got to stay in memory
	p.prog_read(s.c_str());
	if (!p.pfp()) wcout << "unsat" << endl;
	return 0;
}
