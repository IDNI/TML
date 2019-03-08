#include <cstdint>
#include <vector>
#include <forward_list>
#include <iostream>

typedef int64_t int_t;
typedef std::vector<int_t> term;
typedef std::vector<term> matrix;// set of relational terms
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;

const size_t F = 0, T = 1;
const int_t pad = 0;

void bdd_init();

#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))

class lp { // [pfp] logic program
	std::forward_list<matrix> rawrules;
	std::vector<class rule*> rules;
	void step(); // single pfp step
public:
	size_t bits, ar = 0, maxw = 0;
	size_t db = F; // db's bdd root
	bool pfp();
	void printdb(std::wostream& os);
	void rule_add(const matrix& t);
	void compile(size_t bits, size_t nsyms);
	vbools allsat(size_t x);
};
