#include <iostream>
#include <cstdlib>
using namespace std;
int main(int argc, char** argv) {
	if (argc == 1) { cout << "usage: tcgen <# of vertices>" << endl; return 0; }
	size_t n = atol(argv[1]);
	for (size_t k = 1; k < n; ++k)
		cout << "e " << k << ' ' << k+1 << '.' << endl;
	cout << "e " << n << " 1." << endl;
//	cout << "t ?x ?y :- e ?x ?y."<<endl;
//	cout << "t ?x ?y :- t ?x ?z, e ?z ?y."<<endl;
	cout << "e ?x ?y :- e ?x ?z, e ?z ?y."<<endl;
//	cout << "e ?x ?y :- e ?z ?y, e ?x ?z."<<endl;
	return 0;
}
