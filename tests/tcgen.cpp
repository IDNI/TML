#include <iostream>
#include <cstdlib>
using namespace std;
int main(int argc, char** argv) {
	if (argc == 1) { cout << "usage: tcgen <# of vertices>" << endl; return 0; }
	size_t n = atol(argv[1]);
	for (size_t k = 1; k < n; ++k)
		cout << "e " << k << ' ' << k+1 << '.' << endl;
	cout << "e " << n << " 1." << endl;
	cout << "e ?x ?y :- e ?x ?z, e ?z ?y."<<endl;
	return 0;
}
