// #include <cstddef>

struct C {
  int x;
  int y;
};

void test() {
  auto a = __builtin_offsetof(C, y);
  auto b = __builtin_offsetof(C, x);
}
