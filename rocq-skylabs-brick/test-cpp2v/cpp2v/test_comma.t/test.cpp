struct T {
  void operator,(int x) {}
};

void test() {
  T t;
  t, 3;
}
