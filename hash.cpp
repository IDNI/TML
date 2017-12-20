#include "hash.h"
#include "logprimes.h"
#include <cstdlib>

uint64_t lphash(const int32_t& t) {
	uint64_t h = 0;
	size_t len = sizeof(int32_t);
	const unsigned char *c = (const unsigned char*)&t;
	for (size_t n = 0; n < len; ++n)
		h += logprimes[*c] * n; // order dependant
	return h;
}
