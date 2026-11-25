#include "common.hpp"
template <class T> struct M { M &operator=(M &&) = default; W<T> w; };
int f() { return sizeof(M<Bad>); }
