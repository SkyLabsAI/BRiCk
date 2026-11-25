#include "common.hpp"
template <class T> struct I { W<T> w; };
int f() { return sizeof(I<Bad>); }
