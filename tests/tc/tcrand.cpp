#include <iostream>
#include <cstdlib>
#include <map>
#include <set>
#include <ctime>
#include <fstream>
#include <array>
using namespace std;

#define measure_time(x) start = clock(); x; end = clock(); \
	cout << double(end - start) / CLOCKS_PER_SEC << endl

size_t size(const map<int, set<int>>& m) {
	size_t r = 0;
	for (auto x : m) r += x.second.size();
	return r;
}

void tc(map<int, set<int>>& m) {
loop:	size_t sz = size(m);
	set<array<int, 2>> s;
	for (auto x : m)
		for (int y : x.second)
			for (int z : m[y])
				s.insert({x.first, z});
	for (auto x : s) m[x[0]].insert(x[1]);
	if (sz != size(m)) goto loop;
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
	clock_t start, end;
	measure_time(tc(m));
	for (auto x : m)
		for (auto y : x.second)
			out << "e(" << x.first << ' ' << y << ")." << endl;
	return 0;
}
