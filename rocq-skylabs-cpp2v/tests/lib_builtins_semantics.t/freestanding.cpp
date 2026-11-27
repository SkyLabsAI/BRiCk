// Freestanding code can define abs independently of __builtin_abs.
extern "C" int abs(int) { return 7; }
static_assert(__builtin_abs(-3) == 3);
int builtin_call() { return __builtin_abs(-3); }
int ordinary_call() { return abs(-3); }
