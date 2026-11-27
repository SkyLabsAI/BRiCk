namespace C {
extern "C" __SIZE_TYPE__ strlen(const char *s) noexcept;
}
__SIZE_TYPE__ builtin_call(const char *s) { return __builtin_strlen(s); }
__SIZE_TYPE__ ordinary_call(const char *s) { return C::strlen(s); }
