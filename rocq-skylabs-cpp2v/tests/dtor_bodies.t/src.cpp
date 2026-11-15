#include "inc.hpp"

// Using the destructors makes clang define them: cpp2v prints them as
// [Some (CompilerProvided body)].
void test() {
  A a;
  B b;
  T t;
}
