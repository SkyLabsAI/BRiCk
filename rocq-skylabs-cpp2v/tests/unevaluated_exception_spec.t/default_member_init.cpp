#include "common.hpp"
// Issue #507.
// defaulted default ctor of a class template specialization; evaluation
// instantiates the ill-formed default member initializer
template <class T> struct Holder { Holder() = default; Holder(const T &v) : t(v) {} T t{}; };
int f() { Holder<NoDefault> x(NoDefault(1)); return 0; }
