#include "earley.h"

int main() {
	using namespace std;
	
	// Using Elizbeth Scott paper example 2, pg 64
	earley e({
			{"S", { { "b" }, { "S", "S" } } }
			//{"S", { { "" }, { "a", "S", "b", "S" } } },
//			{"S", { { "" }, { "A", "S", "B", "S" } } },
//			{"A", { { "" }, { "A", "a" } } },
//			{"B", { { "b" }, { "B", "b" } } }
		});
	cout << e.recognize("bbb") << endl << endl;
	
	// infinite ambiguous grammar, advanced parsing pdf, pg 86
	// will capture cycles
	earley e1({{"S", { { "b" }, {"S"} }}});
	cout << e1.recognize("b") << endl << endl;

	// another ambigous grammar
	earley e2({ {"S", { { "a", "X", "X", "c" }, {"S"} }},
				{"X", { {"X", "b"}, { "" } } },

	});
	cout << e2.recognize("abbc") << endl << endl;

	// highly ambigous grammar, advanced parsing pdf, pg 89
	earley e3({ {"S", { { "S", "S" }, {"a"} }}
	});
	cout << e3.recognize("aaaaa") << endl << endl;


	//using Elizabeth sott paper, example 3, pg 64.
	earley e4({{"S", { { "A", "T" }, {"a","T"} }},
				{"A", { { "a" }, {"B","A"} }},
				{"B", { { ""} }},
				{"T", { { "b","b","b" } }},
	});
	cout << e4.recognize("abbb") << endl << endl;

	earley e5({{"S", { { "b", }, {"S", "S", "S", "S"}, {""} }}});
	cout << e5.recognize("b") << endl << endl;

	earley e6({{"S", { {"n"}, { "S", "X", "S" }}},
				{"X", { {"p"}, {"m"}}}
	});
	cout << e6.recognize("npnmn") << endl;
/*	cout << e.recognize("aa") << endl << endl;
	cout << e.recognize("aab") << endl << endl;
	cout << e.recognize("abb") << endl << endl;
	cout << e.recognize("aabb") << endl << endl;
	cout << e.recognize("aabbc") << endl << endl;
*/
	return 0;
}
