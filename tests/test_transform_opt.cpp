// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.

#include "test_transform_opt.h"
#include "../src/driver.h"
#include "../src/transform_opt_squaring.h"
#include "../src/transform_opt_cqc.h"

using namespace idni;

TEST_SUITE("transform_opt-squaring") {
	TEST_CASE("squaring: .") {
		flat_prog fp;
		EXPECT_TRUE( square_program(fp).empty() );
	}
	TEST_CASE("squaring: a.") {
		auto fp = flat_prog_f({{{'a'}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 1);
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a'}}));
	}
	TEST_CASE("squaring: a(1).") {
		auto fp = flat_prog_f({{{'a', '1'}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 1);
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1'}}));
	}
	TEST_CASE("squaring: a(1 2).") {
		auto fp = flat_prog_f({{{'a', '1', '2'}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 1);
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}));
	}
	TEST_CASE("squaring: a(1). b(1).") {
		auto fp = flat_prog_f({
			{{'a', '1'}},
			{{'b', '1'}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', '1'}}) );
	}
	TEST_CASE("squaring: a(?x).") {
		auto x = var_f();
		auto fp = flat_prog_f({{{'a', x}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 1 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', x}}) );
	}

	#ifndef ENABLE_WHEN_CONSIDERING_FACTS_IN_UNIFICATION
	TEST_CASE("squaring: a(1). b(x?):-a(x?).") {
		auto x = var_f();
		auto fp = flat_prog_f({
			{{'a', '1'}},
			{{'b', x}, /* :- */ {'a', x}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', '1'}}) );
	}
	TEST_CASE("squaring: a(1 2). b(?x):-a(x? y?). c(?x):-a(y? x?).") {
		auto x = var_f(); auto y = var_f();
		auto fp = flat_prog_f({
			{{'a', '1', '2'}},
			{{'b', x}, /* :- */ {'a', x, y}},
			{{'c', x}, /* :- */ {'a', y, x}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 3 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', '1'}}) );
		EXPECT_TRUE( rules_e(sqr)[2] == rule_f({{'c', '2'}}) );
	}
	TEST_CASE("squaring: a(1 2). b(?x):-a(?x ?x).") {
		auto x = var_f();
		auto fp = flat_prog_f({
			{{'a', '1', '2'}},
			{{'b', x}, /* :- */ {'a', x, x}}});
		auto sqr = square_program(fp);
		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', x},{'a', x, x}}) );
	}
	TEST_CASE("squaring: a(1 2). b(?x):-a(2 ?x).") {
		auto x = var_f();
		auto fp = flat_prog_f({
			{{'a', '1', '2'}},
			{{'b', x}, /* :- */ {'a', '2', x}}});
		auto sqr = square_program(fp);

		#ifndef DELETE_ME
		std::cout << "SQR PROGRAM:"<< std::endl;
		for (auto r: sqr) {
			std::cout << "RULE: {";
			for (auto t: r) {
				for (auto i: t) {
				std::cout << i << ",";
				}
			}
			std::cout << "}" << std::endl;
		}
		#endif // DELETE_ME

		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', '1', '2'}}) );
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', x}, {'a', '2', x}}) );
	}

	#endif // ENABLE_WHEN_CONSIDERING_FACTS_IN_UNIFICATION

	TEST_CASE("squaring:  a(?x ?y):-c(?y). b(?x):-a(?y ?x).") {
		auto x1 = var_f(); auto y1 = var_f(); int_t x2 = -4; int_t y2 = -3;
		auto fp = flat_prog_f({
			{{'a', x1, y1},  /* :- */ {'c', y1}},
			{{'b', x1}, /* :- */ {'a', y1, x1}}});
		auto sqr = square_program(fp);

		#ifndef DELETE_ME
		std::cout << "SQR PROGRAM:"<< std::endl;
		for (auto r: sqr) {
			std::cout << "RULE: {";
			for (auto t: r) {
				for (auto i: t) {
				std::cout << i << ",";
				}
			}
			std::cout << "}" << std::endl;
		}
		#endif // DELETE_ME

		EXPECT_TRUE( sqr.size() == 2 );
		EXPECT_TRUE( rules_e(sqr)[0] == rule_f({{'a', x1, y1}, {'c', y1}}));
		EXPECT_TRUE( rules_e(sqr)[1] == rule_f({{'b', x2}, {'c', y2}}));
	}

}

#ifdef REWRITE_AS_DOCTESTS

//
// UCQProj.tml
//

// http://www.dit.unitn.it/~accord/RelatedWork/GAV&LAV/Information%20Integration%20using%20local%20views.pdf

p(?X ?Z) :- a(?X ?Y), a(?Y ?Z).
p(?X ?Z) :- a(?X ?U), a(?V ?Z).

// http://sparql-qc-bench.inrialpes.fr/UCQProj.html

/*PREFIX :

SELECT ?x WHERE {
   ?x :takesCourse "Course10" . ?x :takesCourse "Course20" .
}*/

Q11(?x) :- takesCourse(?x Course10), takesCourse(?x Course20).

/*PREFIX :

SELECT ?x WHERE {
   ?x :takesCourse "Course10" .
}*/

Q11(?x) :- takesCourse(?x Course10).

/*PREFIX :

SELECT ?x ?y ?z WHERE {
	?x a :Student .
	?x :registeredAt ?y .
	?y a :University .
	?x :placeOfBirth ?z .
	?z a :City .
	?y :locatedAt ?z .
}*/

Q12(?x ?y ?z) :-
  Student(?x),
  registeredAt(?x ?y),
  University(?y),
  placeOfBirth(?x ?z),
  City(?z),
  locatedAt(?y ?z).

/*PREFIX :

SELECT ?x ?y ?z WHERE {
	?x a :Student .
	?x :registeredAt ?y .
	?x :placeOfBirth ?z .
	?y a :University .
	?y :locatedAt ?z .
	?z a :City .
}*/

Q12(?x ?y ?z) :-
  Student(?x),
  registeredAt(?x ?y),
  placeOfBirth(?x ?z),
  University(?y),
  locatedAt(?y ?z),
  City(?z).

/*PREFIX :

SELECT ?x ?y WHERE {
	?x a :Professor .
	?x :graduatedFrom ?y .
	?x :memeberOf ?y
}*/

Q13(?x ?y) :-
  Professor(?x),
  graduatedFrom(?x ?y),
  memberOf(?x ?y).

/*PREFIX :

SELECT ?x ?y WHERE {
	?x a :Professor .
	?x :memeberOf ?y
}*/

Q13(?x ?y) :-
  Professor(?x),
  memberOf(?x ?y).

/*PREFIX :

SELECT ?x   WHERE {
	?x :takesCourse ?c1 .
	?c1 :shortName "Cs200" .
	?x :takesCourse ?c2 .
	?c2 :shortName "Cs301" .
	?x :takesCourse _:b .
	_:b :shortName "Cs401" .
}*/

Q14(?x) :-
  takesCourse(?x ?c1),
  shortName(?c1 Cs200),
  takesCourse(?x ?c2),
  shortName(?c2 Cs301),
  takesCourse(?x ?c3),
  shortName(?c3 Cs401).

/*PREFIX :

SELECT ?x WHERE {
	?x :takesCourse ?c1 .
	?c1 :shortName "Cs200" .
	?x :takesCourse ?c2 .
	?c2 :shortName "Cs301" .
}*/

Q14(?x) :-
  takesCourse(?x ?c1),
  shortName(?c1 Cs200),
  takesCourse(?x ?c2),
  shortName(?c2 Cs301).

/*PREFIX :

SELECT ?x ?y ?z ?t ?s ?ag ?sx ?email ?dept ?course WHERE
{
  ?x a :Student .
  ?x :name ?y .
  ?x :nickName ?z .
  ?x :telephone ?t .
  ?x :ssn ?s .
  ?x :age ?ag .
  ?x :sex ?sx .
  ?x :emailAddress ?email .
  ?x :memberOf ?dept .
  ?x :takesCourse ?course .
}*/

Q17(?x ?y ?z ?t ?s ?ag ?sx ?email ?dept ?course) :-
  Student(?x),
  name(?x ?y),
  nickName(?x ?z),
  telephone(?x ?t),
  ssn(?x ?s),
  age(?x ?ag),
  sex(?x ?sx),
  emailAddress(?x ?email),
  memberOf(?x ?dept),
  takesCourse(?x ?course).

/*PREFIX :

SELECT ?x ?y ?z ?t ?s ?ag ?sx ?email ?dept ?course  WHERE
{
  ?x a :Student .
  ?x :name ?y .
  ?x :nickName ?z .
  ?x :telephone ?t .
  ?x :ssn ?s .
  ?x :age ?ag .
  ?x :sex ?sx .
  ?x :emailAddress ?email .
  ?x :memberOf ?dept .
  ?x :takesCourse ?course .
  ?x :masterDegreeFrom ?master .
}*/

Q17(?x ?y ?z ?t ?s ?ag ?sx ?email ?dept ?course) :-
  Student(?x),
  name(?x ?y),
  nickName(?x ?z),
  telephone(?x ?t),
  ssn(?x ?s),
  age(?x ?ag),
  sex(?x ?sx),
  emailAddress(?x ?email),
  memberOf(?x ?dept),
  takesCourse(?x ?course),
  masterDegreeFrom(?x ?master).

/*PREFIX :

SELECT ?x ?y ?z ?r  WHERE {
	?x :subOrganizationOf ?y .
	?y :subOrganizationOf ?z .
	?z :subOrganizationOf ?r .
	?r :subOrganizationOf :Unibz .
}*/

Q18(?x ?y ?z ?r) :-
  subOrganizationOf(?x ?y),
  subOrganizationOf(?y ?z),
  subOrganizationOf(?z ?r),
  subOrganizationOf(?r Unibz).

/*PREFIX :

SELECT ?x ?y ?z ?r WHERE {
	?x :subOrganizationOf ?y .
	?y :subOrganizationOf ?z .
	?z :subOrganizationOf ?r .
}*/

Q18(?x ?y ?z ?r) :-
  subOrganizationOf(?x ?y),
  subOrganizationOf(?y ?z),
  subOrganizationOf(?z ?r).

/*PREFIX :

SELECT ?x ?z WHERE {
	?x a :GraduateStudent .
	?y a :Department .
	?x :memberOf ?y .
	?y :subOrganizationOf :UniversityO .
	?x :email ?z .
}*/

Q19a(?x ?z) :-
  GraduateStudent(?x),
  Department(?y),
  memberOf(?x ?y),
  subOrganizationOf(?y UniversityO),
  email(?x ?z).

/*PREFIX :

SELECT ?x  ?z WHERE {
	?x a :GraduateStudent .
	?y a :Department .
	?x :memberOf ?y .
	?y :subOrganizationOf :University1 .
	?x :email ?z .
}*/

Q19a(?x ?z) :-
  GraduateStudent(?x),
  Department(?y),
  memberOf(?x ?y),
  subOrganizationOf(?y University1),
  email(?x ?z).

/*PREFIX :

SELECT ?x  ?z WHERE {
	?x a :GraduateStudent .
	?y a :Department .
	?x :memberOf ?y .
	?y :subOrganizationOf ?u .
	?x :email ?z .
}*/

Q19b(?x ?z) :-
  GraduateStudent(?x),
  Department(?y),
  memberOf(?x ?y),
  subOrganizationOf(?y ?u),
  email(?x ?z).

/*PREFIX :

SELECT ?x  ?z WHERE {
	?x a :GraduateStudent .
	?y a :Department .
	?x :memberOf ?y .
	?y :subOrganizationOf :University1 .
	?x :email ?z .
}*/

Q19b(?x ?z) :-
  GraduateStudent(?x),
  Department(?y),
  memberOf(?x ?y),
  subOrganizationOf(?y University1),
  email(?x ?z).

//
// cqnc_test.tml
//

// Examples from Information Integration Using Logical Views
// http://www.dit.unitn.it/~accord/RelatedWork/GAV&LAV/Information%20Integration%20using%20local%20views.pdf

// Example 3: (1) <= (2)

u(?x ?z) :- a(?x ?y), a(?y ?z).
u(?x ?z) :- a(?x ?u), a(?v ?z).

// Example 4: (1) <= (2)

p(?x ?z) :- a(?x ?y), a(?y ?z), ~a(?x ?z).
p(?a ?c) :- a(?a ?b), a(?b ?c), ~a(?a ?d).

j(?x ?z) :- a(?x ?y), a(?y ?z), ~a(?x ?z).
j(?a ?c) :- a(?a ?b), a(?b ?c), ~a(?c ?c).

// Examples from Containment of Conjunctive Queries with Safe Negation
// http://www2.informatik.uni-freiburg.de/~dbis/Publications/03/icdt03.pdf

// Example 1: (1) <= (2)

q(?x ?z) :- a(?x ?y), a(?y ?z), ~a(?x ?z).
q(?a ?c) :- a(?a ?b), a(?b ?c), a(?b ?d), ~a(?a ?d).

// Example 2:

r(?x ?z) :- a(?x ?y), a(?y ?z), ~a(?x ?z).
r(?a ?c) :- a(?a ?b), a(?b ?c), ~b(?c ?c).

// Example 3: (1) <= (2)

s(?a ?c) :- a(?a ?b), a(?b ?c), a(?b ?d).
s(?x ?z) :- a(?x ?y), a(?y ?z).

// Example 4: (1) <= (2)

h() :- a(?x ?y), a(?y ?z), ~a(?x ?z).
h() :- a(?a ?b), a(?c ?d), ~a(?b ?c).

// Example 5:

t() :- a(?x ?y), a(?y ?z), ~a(?x ?z).
t() :- a(?a ?b), a(?c ?d), ~a(?a ?d), ~a(?b ?c).

// http://sparql-qc-bench.inrialpes.fr/UCQProj.html

/*PREFIX :

SELECT ?x WHERE {
   ?x :takesCourse "Course10" . ?x :takesCourse "Course20" .
}*/

Q11(?x) :- takesCourse(?x Course10), takesCourse(?x Course20).

/*PREFIX :

SELECT ?x WHERE {
   ?x :takesCourse "Course10" .
}*/

Q11(?x) :- takesCourse(?x Course10).

/*PREFIX :

SELECT ?x ?y WHERE {
	?x a :Professor .
	?x :graduatedFrom ?y .
	?x :memeberOf ?y
}*/

Q13(?x ?y) :-
  Professor(?x),
  graduatedFrom(?x ?y),
  memberOf(?x ?y).

/*PREFIX :

SELECT ?x ?y WHERE {
	?x a :Professor .
	?x :memeberOf ?y
}*/

Q13(?x ?y) :-
  Professor(?x),
  memberOf(?x ?y).

#endif  // REWRITE_AS_DOCTESTS