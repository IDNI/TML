#include <vector>
#include <map>
#include <set>
#include <array>
#include <iostream>
using namespace std;

typedef int32_t int_t;
typedef array<int_t, 3> node;

class bdds_base {
	vector<node> V;
	map<node, int_t> M;
	int_t root;
	size_t dim = 1;
protected:
	int_t add(const node& n);
	int_t add_nocheck(const node& n);
	bdds_base();
public:
	static const int_t F = 0, T = 1;
	node getnode(size_t n) const {
		if (dim == 1) return V[n];
		const size_t m = n % V.size(), ms = (n / V.size() + 1) * V.size();
		node r = V[m];
		if (!r[0]) {
			if (!r[1]) return V[F];
			return ms == V.size() * dim ? V[T] : V[root];
		} else return r[1] += ms, r[2] += ms, r;
	}
	void setpow(int_t _root, size_t _dim) { root = _root, dim = _dim; }
};

class bdds : public bdds_base {
	template<typename op_t> friend
	int_t bdd_apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op);
	template<typename op_t> friend
	int_t bdd_apply(const bdds& b, int_t x, bdds& r, const op_t& op);
	int_t from_bit(int_t x, bool v);
	int_t from_eq(int_t x, int_t y);

public:
	int_t from_bvec(const vector<bool>& v);
	template<typename K> int_t from_vec(K* v, size_t len, size_t bits, bool discard_zero, bool negfst);
	template<typename K> int_t from_vec(vector<K> v, size_t bits, bool discard_zero, bool negfst);
	template<typename K> int_t from_query(const vector<const vector<K>>& v,
						size_t bits, size_t max_len);
	void out(wostream& os, const node& n) const;
	void out(wostream& os, size_t) const;
	int_t bdd_or(int_t x, int_t y);
	int_t bdd_and(int_t x, int_t y);
	int_t bdd_and_not(int_t x, int_t y);
};

struct op_set : public set<int_t> {
	typedef set<int_t> base;
	using base::base;
	node operator()(const bdds& b, const node& n) const {
		return find(n[0]) == end() ? n : b.getnode(n[1]);
	}
}; 
struct op_unset : public set<int_t> {
	typedef set<int_t> base;
	using base::base;
	node operator()(const bdds& b, const node& n) const {
		return find(n[0]) == end() ? n : b.getnode(n[2]);
	}
};

template<typename X, typename Y>
struct op_compose {
	X x;
	Y y;
	op_compose(){}
	op_compose(const X& x, const Y& y) : x(x), y(y) {}
	node operator()(const bdds& b, const node& n) const { return x(b, y(b, n)); }
};

struct op_set_unset : public op_compose<op_set, op_unset> {
	op_set_unset(const set<int_t>& s, const set<int_t>& us) :
		op_compose(op_set(s.begin(), s.end()), op_unset(us.begin(), us.end())) {}
};

template<typename op_t>
int_t bdd_apply(const bdds& b, int_t x, bdds& r, const op_t& op) {
	node n = op(b, b.getnode(x));
	if (n[1] > 1) n[1] = bdd_apply(b, n[1], r, op);
	if (n[2] > 1) n[2] = bdd_apply(b, n[2], r, op);
	return r.add(n);
}

template<typename op_t>
int_t bdd_apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, const op_t& op) {
	const node &Vx = bx.getnode(x), &Vy = by.getnode(y);
	const int_t &vx = Vx[0], &vy = Vy[0];
	int_t v = vx, a, b, c, d;
	if (!vx) {
		if (!vy) return op(Vx[1], Vy[1]);
		else	a = c = x, b = Vy[1], d = Vy[2], v = vy;
	} else if (!vy)	a = Vx[1], b = d = y, c = Vx[2];
	else if (vx==vy)a = Vx[1], b = Vy[1], c = Vx[2], d = Vy[2];
	else if (vx<vy)	a = Vx[1], b = d = y, c = Vx[2];
	else		a = c = x, b = Vy[1], d = Vy[2], v = vy;
	return r.add({v, bdd_apply(bx, a, by, b, r, op), bdd_apply(bx, c, by, d, r, op)});
}

struct op_or { int_t operator()(int_t x, int_t y) const { return (x||y)?1:0; } }; 
struct op_and { int_t operator()(int_t x, int_t y) const { return (x&&y)?1:0; } }; 
struct op_and_not { int_t operator()(int_t x, int_t y) const { return (x&&!y)?1:0; } }; 
int_t bdds::bdd_or(int_t x, int_t y) {
	static constexpr op_or op;
	return bdd_apply(*this, x, *this, y, *this, op);
}
int_t bdds::bdd_and(int_t x, int_t y) {
	static constexpr op_and op;
	return bdd_apply(*this, x, *this, y, *this, op);
}
int_t bdds::bdd_and_not(int_t x, int_t y) {
	static constexpr op_and_not op;
	return bdd_apply(*this, x, *this, y, *this, op);
}

int_t bdds::from_bvec(const vector<bool>& v) {
	int_t k = T, n = v.size() - 1;
	do { k = v[n] ? add({n+1, k, F}) : add({n+1, F, k}); } while (n--);
	//for (n = 0; n < v.size(); ++n) k = v[n] ? add({n+1, k, F}) : add({n+1, F, k});
	return k;
}

template<typename K>
int_t bdds::from_vec(K* v, size_t len, size_t bits, bool discard_zero, bool negfst) {
	int_t k = T, t = bits * len;
	bool b = false;
	if (negfst && *v < 0) *v = -*v, b = true;
	for (size_t bit = bits-1, n = len - 1;; n = len - 1) {
		do {
			if (!discard_zero || v[n])
				k = v[n]&(1<<bit) ? add({t, k, F}) : add({t, F, k});
		} while (--t, n--);
		if (!bit--) return b ? *v = -*v, bdd_and_not(T, k) : k;
	}
}

template<typename K>
int_t bdds::from_vec(vector<K> v, size_t bits, bool discard_zero, bool negfst) {
	return from_vec(&v[0], v.size(), bits, discard_zero, negfst);
} 

int_t bdds::from_bit(int_t x, bool v) { return add(v ? node{x, T, F} : node{x, F, T}); }

int_t bdds::from_eq(int_t x, int_t y) {
	return bdd_or(	bdd_and(from_bit(x, true), from_bit(y, true)),
			bdd_and(from_bit(x, false),from_bit(y, false)));
}

template<typename K>
set<int_t> getbits(K k, size_t bits) {
	set<int_t> r;
	do { r.emplace(k & (1 << --bits) ? bits : -bits); } while (bits);
	return r;
}

template<typename K>
int_t bdds::from_query(const vector<const vector<K>>& v, size_t bits, size_t max_len) {
	int_t e = T;
	size_t base = 0, sz = v.size() * max_len, var = 0;
	map<int_t, size_t> m;
	K *t = (K*)memset(new K[sz], 0, sz * sizeof(K)), *u = t;
	for (const vector<K>& x : v) {
		for (const K& y : x) // add syms only
			if (y < 0) *t++ = -y;
			else if (auto it = m.find(y); it != m.end())
				e = bdd_and(e, from_eq(y, it->second));
			else m.emplace(y, ++var);
		if (((t-u) % max_len)) t += max_len - (t-u) % max_len;
	}
	return bdd_and(e, from_vec(t, sz, bits, true));
}

void bdds::out(wostream& os, size_t n) const { out(os, getnode(n)); }
void bdds::out(wostream& os, const node& n) const {
	if (!n[0]) os << (n[1] ? L'T' : L'F');
	else out(os << n[0] << L'?', getnode(n[1])), out(os << L':', getnode(n[2]));
}

bdds_base::bdds_base() { add_nocheck({0, 0, 0}), add_nocheck({0, 1, 1}); }

int_t bdds_base::add_nocheck(const node& n) { return V.emplace_back(n), M[n]=V.size()-1; }

int_t bdds_base::add(const node& n) {
	if (n[1] == n[2]) return n[1];
	auto it = M.find(n);
	return it == M.end() ? add_nocheck(n) : it->second;
}

int main() {
	bdds b;
	int_t t = b.from_bvec({ 1, 0, 1, 0, 1, 0, 0, 0 });
	b.out(wcout, t);
	wcout << endl;
	int_t s = b.from_bvec({ 0, 0, 1, 1 });
	b.out(wcout, s);
	wcout << endl;
	b.out(wcout, b.bdd_or(b.from_bvec({0,0}),b.from_bvec({1,1}))); wcout << endl;
	b.out(wcout, b.bdd_and(b.from_bvec({0,0}),b.from_bvec({1,1}))); wcout << endl;
	// denomstrate that we assume infinitely many zeros after each string
	// so the length is up to the user
	b.out(wcout, b.bdd_and_not(b.from_bvec({1,1}),b.from_bvec({1,1,1}))); wcout << endl;
	b.out(wcout, b.bdd_and_not(1, b.from_bvec({0,0}))); wcout << endl; // negation
	bdds c; // demonstrate output to another bddset (this is a substitute for gc)
	c.out(wcout, bdd_apply(b, 1, b, b.from_bvec({0,0}), c, op_and_not())); wcout << endl;
	c.out(wcout, bdd_apply(c, 1, b, b.from_bvec({0,0}), c, op_and_not())); wcout << endl;
	c.out(wcout, bdd_apply(bdds(), 1, b, b.from_bvec({0,0}), c, op_and_not())); wcout << endl;
//	int_t v1,v2,v3,v4;
//	wcin >> v1 >> v2 >> v3 >> v4;
//	b.out(wcout, b.bdd_and_not(b.from_bvec({v1,v2}),b.from_bvec({v3,v4}))); wcout << endl;
	int_t x = b.from_vec<int>({1},3, false, false);
	b.out(wcout, x); wcout << endl;
	op_set o;
	o.emplace(2);
	b.out(wcout, bdd_apply(b, x, b, o)); wcout << endl;
	op_unset uo;
	uo.emplace(2);
	b.out(wcout, bdd_apply(b, x, b, uo)); wcout << endl;
//	int_t y = b.from_vec<int>({2,3,4},3);
//	int_t z = b.from_vec<int>({4,5,6},3);
//	b.out(wcout, b.bdd_or(x, b.bdd_or(y, z))); wcout << endl;
	return 0;
}
