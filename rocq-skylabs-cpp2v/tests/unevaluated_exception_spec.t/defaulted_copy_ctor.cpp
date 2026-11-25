#include "common.hpp"
// explicitly defaulted copy ctor; evaluation instantiates W<Bad>'s noexcept-specifier
template <class T> struct C { C() = default; C(const C &) = default; W<T> w; };
int f() { return sizeof(C<Bad>); }
