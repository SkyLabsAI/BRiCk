#include "common.hpp"
// same, reached through a non-template class's defaulted default ctor
template <class T> struct Holder { Holder() = default; Holder(const T &v) : t(v) {} T t{}; };
struct S { Holder<NoDefault> h; S() = default; S(int i) : h(NoDefault(i)) {} };
int f() { S s(1); return 0; }
