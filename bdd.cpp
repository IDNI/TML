#include <vector>
#include <map>
#include <array>
#include <forward_list>
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
	bdds() { add({0, 0, 0}), add({0, 1, 1}); }
	int_t from_bvec(const vector<bool>& v);
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
int_t bdds::bdd_or(int_t x, int_t y) { return bdd_apply(*this, x, *this, y, *this, op_or()); }
int_t bdds::bdd_and(int_t x, int_t y) { return bdd_apply(*this, x, *this, y, *this, op_and()); }
int_t bdds::bdd_and_not(int_t x, int_t y) { return bdd_apply(*this,x,*this,y,*this, op_and_not()); }

int_t bdds::from_bvec(const vector<bool>& v) {
	int_t k = T, n = v.size() - 1;
	do { k = v[n] ? add({n+1, k, F}) : add({n+1, F, k}); } while (n--);
	return k;
}

void bdds::out(wostream& os, size_t n) const { out(os, V[n]); }
void bdds::out(wostream& os, const node& n) const {
	if (!n[0]) os << (n[1] ? L'T' : L'F');
	else {
		os << n[0] << L'?';
		out(os, V[n[1]]), os << L':';
		out(os, V[n[2]]);
	}
}

int_t bdds::add_nocheck(const node& n){
	return V.emplace_back(n), M[n]=V.size()-1;
}

int_t bdds::add(const node& n) {
	auto it = M.find(n);
	return it == M.end() ? add_nocheck(n) : it->second;
}

int main() {
	bdds b;
	size_t t = b.from_bvec({ 1, 0, 1, 0, 1, 0, 0, 0 });
	b.out(wcout, t);
	wcout << endl;
	size_t s = b.from_bvec({ 0, 0, 1, 1 });
	b.out(wcout, s);
	wcout << endl;
	//size_t d = b.bdd_or(s, t);
	b.out(wcout, b.bdd_or(b.from_bvec({0,0}),b.from_bvec({1,1})));
	wcout << endl;
	return 0;
}
