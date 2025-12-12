auto foo() { return 0ULL; }

class F {
  int foo() { return 0; }
  auto bar() { return foo(); }
  auto baz();
};

auto F::baz() { return foo(); }
