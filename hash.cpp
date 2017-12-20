#include "hash.h"
#include "logprimes.h"
#include <cstdlib>

uint64_t lphash(const int32_t& t) {
	uint64_t h = 0;
	const unsigned char *c = (const unsigned char*)&t;
	h += logprimes[*c++];
	h += logprimes[*c++] * 2;
	h += logprimes[*c++] * 3;
	return h + logprimes[*c] * 4;
}
