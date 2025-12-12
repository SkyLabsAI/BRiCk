void test() {
  using T = int[10];
  using CT = const int[10];

  T a{};
  CT b{};
  const T c{};
  const CT d{};
}

template<typename T>
void f() { T arr[10]{}; const T arr2[10]{}; }


void test_template() {
  f<int>();
  f<const int>();
}
