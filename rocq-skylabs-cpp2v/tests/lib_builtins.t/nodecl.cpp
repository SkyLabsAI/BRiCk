// Library builtins without a declaration of the library function.
void m(char *d, const char *s) { __builtin_memcpy(d, s, 4); }
void m2(char *d, const char *s) { __builtin_memcpy(d, s, 2); }
unsigned long l(const char *s) { return __builtin_strlen(s); }
void c(char *d, const char *s) {
  __builtin___memcpy_chk(d, s, 4, __builtin_object_size(d, 0));
}
