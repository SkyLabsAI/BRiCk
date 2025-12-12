struct C {
  int data;
  C(int x):data(x) {}
};

struct D : C {
  int dd;
  using C::C;
};


void test() {
  D d(0);
}
