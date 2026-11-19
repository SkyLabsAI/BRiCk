#include "inc.hpp"

// Using the destructors makes clang define them with empty bodies: cpp2v
// still prints them as [Some Defaulted].
void test() {
  A a;
  B b;
  T t;
}
