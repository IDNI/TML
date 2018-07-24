#include "dict.h"
#include "macros.h"
#include <string.h>

static struct dict_t {
	const wchar_t* s;
	uint32_t h;
	int32_t id;
	struct dict_t *l, *r;
} *dict = 0;

static wchar_t **gconsts = 0, **gvars = 0;
static void **vardata = 0, **constsdata = 0;
static size_t gnconsts = 0, gnvars = 0;

static uint32_t hash(const wchar_t* s) {
	uint32_t h = 1;
	while (*s) h *= 1 + *s * __builtin_bswap32(*s), ++s;
	return h;
}

static int32_t _str_to_id(struct dict_t **d, const wchar_t* s) {
	uint32_t h = hash(s);
	size_t *sz;
	wchar_t*** a;
	void*** data;
	if (*s == L'?') sz = &gnvars, a = &gvars, data = &vardata;
	else sz = &gnconsts, a = &gconsts, data = &constsdata;
	return	!*d ?
			array_append(*a, const wchar_t*, *sz, s=wcsdup(s)),
			*data = realloc(*data, sizeof(void*)**sz),
			data[*sz-1] = 0,
			(*(*d = new(struct dict_t)) = 
				(struct dict_t){ .s=s, .h=h,
				.id = *s==L'?'?*sz:-*sz, .l=0, .r=0 }).id
			: h == (**d).h && !wcscmp((**d).s, s) ? (**d).id
			: _str_to_id((**d).h < h ? &(**d).l : &(**d).r, s);
}

const wchar_t* str_from_id(int32_t id) {
	return id < 0 ? gconsts[-id-1] : gvars[id-1];
}

int32_t str_to_id(const wchar_t* s) { return _str_to_id(&dict, s); }

void id_set_data(int32_t id, void* data) {
	if (id > 0) vardata[id] = data; else constsdata[-id] = data;
}

void* id_get_data(int32_t id) {
	return id > 0 ? vardata[id] : constsdata[-id];
}
