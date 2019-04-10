#include <iostream>
#include <cstdlib>
#include <map>
#include <set>
#include <ctime>
#include <fstream>
#include <array>
using namespace std;

void tc(map<int, set<int>>& m) {
	size_t sz = m.size();
	set<array<int, 2>> s;
	for (auto x : m)
		for (int y : x.second)
			for (int z : m[y])
				s.insert({x.first, z});
	for (auto x : s) m[x[0]].insert(x[1]);
	s.clear();
	if (sz != m.size()) tc(m);
}

int main(int argc, char** argv) {
	if (argc != 5) {
		cout << "usage: tcrand <# of vertices> <# of edges> <file to write input to> <file to write output to>" << endl;
		return 0;
	}
	srand(time(0));
	size_t v = atol(argv[1]), e = atol(argv[2]);
	map<int, set<int>> m;
	while (--e) if (!m[rand() % v].insert(rand() % v).second) ++e;
	ofstream in(argv[3]), out(argv[4]);
	for (auto x : m)
		for (auto y : x.second)
			in << "e(" << x.first << ' ' << y << ")." << endl;
	in << "e(?x ?y) :- e(?x ?z), e(?z ?y)."<<endl;
	tc(m);
	for (auto x : m)
		for (auto y : x.second)
			out << "e(" << x.first << ' ' << y << ")." << endl;
	return 0;
}
