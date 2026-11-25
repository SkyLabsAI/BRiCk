#include "common.hpp"
// user-declared destructor without noexcept-specifier: clang defers its spec too
template <class T> struct U { ~U() {} W<T> w; };
int f() { return sizeof(U<Bad>); }
