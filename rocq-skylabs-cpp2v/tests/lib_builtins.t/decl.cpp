// A library builtin with a declaration of the library function.
#include <cstring>
void m(char *d, const char *s) { __builtin_memcpy(d, s, 4); }
void o(char *d, const char *s) { memcpy(d, s, 4); }
