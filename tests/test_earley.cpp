#include "earley.h"
#include "options.h"

using std::basic_ostringstream,
	std::stringstream,
	std::ofstream,
	std::cout,
	std::endl;

template <typename CharT>
int test_out(int c, earley<CharT> &e){
	stringstream ptd;
	stringstream ssf;

	ssf<<"graph"<<c<<".dot";
	ofstream file(ssf.str());
	e.to_dot(ptd);
	file << ptd.str();
	file.close();
	ssf.str({});
	ptd.str({});
	
	ssf<<"parse_graph"<<c<<".tml";
	ofstream file1(ssf.str());
	e.to_tml_facts(ptd);
	file1 << ptd.str();
	file1.close();
	ssf.str({});
	ptd.str({});
	
	ssf<<"parse_rules"<<c<<".tml";
	ofstream file2(ssf.str());
	e.to_tml_rule(ptd);
	file2 << ptd.str();
	file2.close();

	return 1;
}

int main(int argc, char** argv) {
	using namespace std;
	inputs ii;
	outputs oo;
	o::init_outputs(oo);
	oo.target("debug",  "@stderr");
	oo.target("info",   "@stderr");
	oo.target("error",  "@stderr");
	oo.target("output", "@stdout");
	options o(argc, argv, &ii, &oo);
	bool binlr = o.enabled("bin-lr");

	size_t c = 0;
	// Using Elizbeth Scott paper example 2, pg 64
	earley<char> e({
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
	earley<char> e1({{"start", { { "b" }, {"start"} }}}, binlr);
	cout << e1.recognize("b") << endl << endl;
	test_out(c++, e1);	
	

	// another ambigous grammar
	earley<char> e2({ {"start", { { "a", "X", "X", "c" }, {"start"} }},
				{"X", { {"X", "b"}, { "" } } },

	}, binlr);
	cout << e2.recognize("abbc") << endl << endl;
	test_out(c++, e2);	
	

	// highly ambigous grammar, advanced parsing pdf, pg 89
	earley<char> e3({ {"start", { { "start", "start" }, {"a"} }}
	}, binlr);
	cout << e3.recognize("aaaaa") << endl << endl;
	test_out(c++, e3);

	//using Elizabeth sott paper, example 3, pg 64.
	earley<char> e4({{"start", { { "A", "T" }, {"a","T"} }},
				{"A", { { "a" }, {"B","A"} }},
				{"B", { { ""} }},
				{"T", { { "b","b","b" } }},
	}, binlr);
	cout << e4.recognize("abbb") << endl << endl;
	test_out(c++, e4);

	earley<char> e5({{"start", { { "b", }, {"start", "start", "start", "start"}, {""} }}}, binlr);
	cout << e5.recognize("b") << endl << endl;
	test_out(c++, e5);

	earley<char> e6({{"start", { {"n"}, { "start", "X", "start" }}},
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

	earley<char32_t> e7({ { U"start", {
		{ U"τ" },
		{ U"ξεσκεπάζω"},
		{ U"žluťoučký" },
		{ U"ᚠᛇᚻ᛫ᛒᛦᚦ᛫ᚠᚱᚩᚠᚢᚱ᛫ᚠᛁᚱᚪ᛫ᚷᛖᚻᚹᛦᛚᚳᚢᛗ" },
		{ U"start", U"start" }
	} } }, binlr);
	cout << e7.recognize(U"τžluťoučkýτᚠᛇᚻ᛫ᛒᛦᚦ᛫ᚠᚱᚩᚠᚢᚱ᛫ᚠᛁᚱᚪ᛫ᚷᛖᚻᚹᛦᛚᚳᚢᛗτξεσκεπάζωτ") << endl << endl;
	test_out(c++, e7);

	return 0;
}
