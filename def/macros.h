#include <stdint.h>
#include <stdlib.h>

#define new(x) malloc(sizeof(x))
#define int_t intptr_t
#define array_append(a, t, l, x) ((((t*)(a = realloc(a, sizeof(t)*(l+1))))[l] = x), ++l)
#define array_append_zeros(a, t, l, s) memset(((t*)realloc(a,sizeof(t)*(l+s)))+s,0,sizeof(t)*s),l+=s
#define podcmp(x, y, t) memcmp(&(x), &(y), sizeof(t))
