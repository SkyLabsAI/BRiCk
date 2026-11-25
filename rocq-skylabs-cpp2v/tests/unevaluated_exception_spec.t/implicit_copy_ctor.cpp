#include "common.hpp"
// implicit copy ctor, declared eagerly because W's copy ctor is user-declared
struct I { W<Bad> w; };
int f() { return sizeof(I); }
