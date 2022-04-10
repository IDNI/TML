#include "earley.h"
#include "options.h"
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

int main(int argc, char** argv) {
	using namespace std;
	outputs oo;
	inputs ii;
	oo.target("debug",  "@stderr");  // o::dbg()
	oo.target("info",   "@stderr");  // o::inf()
	oo.target("error",  "@stderr");  // o::err()
	oo.target("output", "@stdout");  // o::out()
	o::dbg() << "DBG" << std::endl;
	o::inf() << "INF" << std::endl;
	o::err() << "ERR" << std::endl;
	o::out() << "OUT" << std::endl;
	options o(argc, argv, &ii, &oo);
	bool binlr = o.enabled("bin-lr");
		
	size_t c = 0;
	// Using Elizbeth Scott paper example 2, pg 64
	earley e({
			{"start", { { "b" }, { "start", "start" } } }
			//{"start", { { "" }, { "a", "start", "b", "start" } } },
//			{"start", { { "" }, { "A", "start", "B", "start" } } },
//			{"A", { { "" }, { "A", "a" } } },
//			{"B", { { "b" }, { "B", "b" } } }
		} , binlr);
	cout << e.recognize("bbb") << endl << endl;
	test_out(c++, e);	
	
	
	// infinite ambiguous grammar, advanced parsing pdf, pg 86
	// will capture cycles
	earley e1({{"start", { { "b" }, {"start"} }}}, binlr);
	cout << e1.recognize("b") << endl << endl;
	test_out(c++, e1);	
	

	// another ambigous grammar
	earley e2({ {"start", { { "a", "X", "X", "c" }, {"start"} }},
				{"X", { {"X", "b"}, { "" } } },

	}, binlr);
	cout << e2.recognize("abbc") << endl << endl;
	test_out(c++, e2);	
	

	// highly ambigous grammar, advanced parsing pdf, pg 89
	earley e3({ {"start", { { "start", "start" }, {"a"} }}
	}, binlr);
	cout << e3.recognize("aaaaa") << endl << endl;
	test_out(c++, e3);

	//using Elizabeth sott paper, example 3, pg 64.
	earley e4({{"start", { { "A", "T" }, {"a","T"} }},
				{"A", { { "a" }, {"B","A"} }},
				{"B", { { ""} }},
				{"T", { { "b","b","b" } }},
	}, binlr);
	cout << e4.recognize("abbb") << endl << endl;
	test_out(c++, e4);

	earley e5({{"start", { { "b", }, {"start", "start", "start", "start"}, {""} }}}, binlr);
	cout << e5.recognize("b") << endl << endl;
	test_out(c++, e5);

	earley e6({{"start", { {"n"}, { "start", "X", "start" }}},
				{"X", { {"p"}, {"m"}}}
	}, binlr);
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
