#include "inc.hpp"
#include "inc2.hpp"

int use_headers() {
    collide_in_class value{};
    foo();
    bar();
    bar2();
    return test_inc() + test_inc2() + get1() + get2() + z.zz + y.zz +
           collide_in_function() + (value.p1 == nullptr) +
           (value.p2 == nullptr) + (collide_ns::p3 == nullptr) +
           (collide_ns::p4 == nullptr);
}
