void test() {
  auto glam = [](auto& l, auto r) {
    l += r;
  };
  int x = 0;
  glam(x, 7);
  long long y = 7;
  glam(y, 42);
}
