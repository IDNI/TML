#include "earley.h"

int test_out(int c, earley &e){
	std::stringstream ssf;
	ssf<<"graph"<<c << ".dot";
	std::ofstream file(ssf.str());
	e.to_dot(file);	
	file.close();
	ssf.str("");

	ssf<<"parse_graph"<<c << ".tml";
	std::ofstream file1(ssf.str());
	e.to_tml_facts(file1);	
	file1.close();
	ssf.str("");

	ssf<<"parse_rules"<<c << ".tml";
	std::ofstream file2(ssf.str());
	e.to_tml_rule(file2);	
	file2.close();

	return 1;

}
int main() {
	using namespace std;
	size_t c = 0;
	// Using Elizbeth Scott paper example 2, pg 64
	earley e({
			{"start", { { "b" }, { "start", "start" } } }
			//{"start", { { "" }, { "a", "start", "b", "start" } } },
//			{"start", { { "" }, { "A", "start", "B", "start" } } },
//			{"A", { { "" }, { "A", "a" } } },
//			{"B", { { "b" }, { "B", "b" } } }
		});
	cout << e.recognize("bbb") << endl << endl;
	test_out(c++, e);	
	
	
	// infinite ambiguous grammar, advanced parsing pdf, pg 86
	// will capture cycles
	earley e1({{"start", { { "b" }, {"start"} }}});
	cout << e1.recognize("b") << endl << endl;
	test_out(c++, e1);	
	

	// another ambigous grammar
	earley e2({ {"start", { { "a", "X", "X", "c" }, {"start"} }},
				{"X", { {"X", "b"}, { "" } } },

	});
	cout << e2.recognize("abbc") << endl << endl;
	test_out(c++, e2);	
	

	// highly ambigous grammar, advanced parsing pdf, pg 89
	earley e3({ {"start", { { "start", "start" }, {"a"} }}
	});
	cout << e3.recognize("aaaaa") << endl << endl;
	test_out(c++, e3);

	//using Elizabeth sott paper, example 3, pg 64.
	earley e4({{"start", { { "A", "T" }, {"a","T"} }},
				{"A", { { "a" }, {"B","A"} }},
				{"B", { { ""} }},
				{"T", { { "b","b","b" } }},
	});
	cout << e4.recognize("abbb") << endl << endl;
	test_out(c++, e4);

	earley e5({{"start", { { "b", }, {"start", "start", "start", "start"}, {""} }}});
	cout << e5.recognize("b") << endl << endl;
	test_out(c++, e5);

	earley e6({{"start", { {"n"}, { "start", "X", "start" }}},
				{"X", { {"p"}, {"m"}}}
	});
	cout << e6.recognize("npnmn") << endl;
	test_out(c++, e6);
/*	cout << e.recognize("aa") << endl << endl;
	cout << e.recognize("aab") << endl << endl;
	cout << e.recognize("abb") << endl << endl;
	cout << e.recognize("aabb") << endl << endl;
	cout << e.recognize("aabbc") << endl << endl;
*/
	return 0;
}
