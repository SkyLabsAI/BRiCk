#include "common.hpp"
template <class T> struct D { ~D() = default; W<T> w; };
int f() { return sizeof(D<Bad>); }
