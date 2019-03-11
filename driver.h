#include "tml.h"

class driver {
	int_t str_read(wstr *s); // parse a string and returns its dict id
	term term_read(wstr *s); // read raw term (no bdd)
	matrix rule_read(wstr *s); // read raw rule (no bdd)
	std::vector<lp*> progs;
	std::vector<std::set<matrix>> proofs;
	bool mult;
	bool pfp(lp *p, std::set<matrix>* proof);
public:
	DBG(driver();)
	lp* prog_read(wstr *s, bool proof);
	void progs_read(wstr s, bool proof);
	lp* prog_create(std::set<matrix> m, bool proof);
	bool pfp(bool proof);
	std::wostream& printbdd(std::wostream& os, const lp& p, size_t t) const;
	std::wostream& printbdd(std::wostream& os, const matrix& t) const;
	std::wostream& printbdd(std::wostream& os, size_t t) const;
	std::wostream& printdb(std::wostream& os, lp *q) const;
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printbdd(std::wostream& os, size_t t) {
	return drv->printbdd(os, t);
}
#endif
