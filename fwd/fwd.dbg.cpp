#include "fwd.h"

using namespace std;

ostream& operator<<(ostream& os, const env& e) {
	return os;
//	os << "{ ";
//	for (int_t n = 0; n < (int_t)e.size(); ++n)
//		if (e[n]) os << -n-1 << '=' << e[n] << ' ';
//	return os << '}';
}

ostream& operator<<(ostream& os, const term& t) {
	os << "( "; for (int_t i : t) os << i << ' ';
	return os << ')';
}

ostream& operator<<(ostream& os, const terms& s) {
	for (const term &t : s) os << t << ' ';
	return os << endl;
}

void fwd::print_clauses() {
	for (size_t k, n = 0; n < negs.size(); ++n) {
		for (k = 0; k < negs[n].size(); ++k) cout << negs[n][k] << ' ';
		cout << " => ";
		for (k = 0; k < poss[n].size(); ++k) cout << poss[n][k] << ' ';
		cout << endl;
	}
}

void fwd::print_matches() {
	for (auto x : p2n)
		for (auto y : x.second)
			cout << "p "<<poss[x.first.first][x.first.second]
			<<" matches n "<< negs[y.first][y.second]<<endl;
}

int main(int, char**) {
	// -1 1 -1 -> -1 -2
	// -1 -2, -1 2 -> -1 3
	// 1 1 1
	// 2 1 1
	terms f = {{1,1,1},{2,1,1}};
	fwd w({{{-1,1,-1}},{{-1,-2},{-1,2}}},{{{-1,2}},{{-1,3}}});
	w(f);
	cout << f;
}
