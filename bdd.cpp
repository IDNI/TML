#include <vector>
#include <map>
#include <array>
#include <iostream>
using namespace std;

typedef int32_t int_t;
typedef array<int_t, 3> node;

class bdds {
	vector<node> V;
	map<node, int_t> M;
	static const int_t F = 0, T = 1;//, nvars, dim;
	int_t add(const node& n);
	int_t add_nocheck(const node& n);
	template<typename op_t> friend
	int_t bdd_apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, op_t op);
public:
	bdds();
	int_t from_bvec(const vector<bool>& v);
	template<typename K> int_t from_vec(const K* v, size_t len, size_t bits);
	template<typename K> int_t from_vec(const vector<K>& v, size_t bits);
	void out(wostream& os, const node& n) const;
	void out(wostream& os, size_t) const;
	int_t bdd_or(int_t x, int_t y);
	int_t bdd_and(int_t x, int_t y);
	int_t bdd_and_not(int_t x, int_t y);
};

template<typename op_t>
int_t bdd_apply(const bdds& bx, int_t x, const bdds& by, int_t y, bdds& r, op_t op) {
	const auto &Vx = bx.V[x], &Vy = by.V[y];
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
int_t bdds::from_vec(const K* v, size_t len, size_t bits) {
	int_t k = T, t = bits * len;
	for (size_t bit = bits-1, n = len - 1;; n = len - 1) {
		do {
			k = v[n]&(1<<bit)? add({t--, k, F})
					 : add({t--, F, k});
		} while (n--);
		if (!bit--) return k;
	}
}
template<typename K>
int_t bdds::from_vec(const vector<K>& v, size_t bits) {
	return from_vec(&v[0], v.size(), bits);
}

void bdds::out(wostream& os, size_t n) const { out(os, V[n]); }
void bdds::out(wostream& os, const node& n) const {
	if (!n[0]) os << (n[1] ? L'T' : L'F');
	else out(os << n[0] << L'?', V[n[1]]), out(os << L':', V[n[2]]);
}

bdds::bdds() { add_nocheck({0, 0, 0}), add_nocheck({0, 1, 1}); }

int_t bdds::add_nocheck(const node& n) { return V.emplace_back(n), M[n]=V.size()-1; }

int_t bdds::add(const node& n) {
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
	int_t x = b.from_vec<int>({1},3);
	b.out(wcout, x); wcout << endl;
//	int_t y = b.from_vec<int>({2,3,4},3);
//	int_t z = b.from_vec<int>({4,5,6},3);
//	b.out(wcout, b.bdd_or(x, b.bdd_or(y, z))); wcout << endl;
	return 0;
}
