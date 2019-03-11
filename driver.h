#include "tml.h"

class driver {
	int_t str_read(wstr *s); // parse a string and returns its dict id
	term term_read(wstr *s); // read raw term (no bdd)
	matrix rule_read(wstr *s); // read raw rule (no bdd)
	std::vector<lp*> progs;
	bool mult;
	bool pfp(lp *p);
public:
	DBG(driver();)
	lp* prog_read(wstr *s);
	void progs_read(wstr s);
	bool pfp();
	std::wostream& printbdd(std::wostream& os, const matrix& t) const;
	std::wostream& printbdd(std::wostream& os, size_t t) const;
	std::wostream& printdb(std::wostream& os) const;
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printbdd(std::wostream& os, size_t t) {
	return drv->printbdd(os, t);
}
#endif
