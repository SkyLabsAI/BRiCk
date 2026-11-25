#include "common.hpp"
// C++20 defaulted comparison
template <class T> struct E { W<T> w; bool operator==(const E &) const = default; };
int f() { return sizeof(E<Bad>); }
