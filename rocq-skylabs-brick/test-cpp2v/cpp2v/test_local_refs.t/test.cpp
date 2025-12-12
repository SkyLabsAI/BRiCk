template<typename T>
void foo(T y) {
  T x = y;
  x = y;
}

struct C {};

void test() {
  C c;
  foo<C>(c);
  foo<C&>(c);
  int x{};
  foo<int>(x);
  foo<int&>(x);
}
