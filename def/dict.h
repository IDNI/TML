#include <wchar.h>
#include <stdint.h>
#include "macros.h"

int32_t str_to_id(const wchar_t* s);
const wchar_t* str_from_id(int32_t id);
void id_set_data(int32_t id, void* data);
void* id_get_data(int32_t id);
wint_t str_read(int_t *r);
