void test() {
  int t{0};
  int asdf{9};
  int a = t + asdf;
  int &r = a;
  auto x = [&](int x) { t++; return t + asdf; };
  auto x_val = [=](int x) { return t + asdf + x; };
  auto x_mut = [=](int x) mutable { t++; return t + asdf + x; };
  auto x_ref = [&](int y) { return r + y; };
  auto x_ref_val = [=](int y) { return r + y; };
}

struct C {
  C() = delete;
  ~C() = delete;
  C(C&) = delete;
  C(C&&) = delete;
  int x;
  void test() {
    auto lam = [&]() { return x; };
    auto lam_val = [=]() { return x; };
    lam();
  }
  void test_const() const {
    auto lam = [&]() { return x; };
    auto lam_val = [=]() { return x; };
    lam();
  }
};
