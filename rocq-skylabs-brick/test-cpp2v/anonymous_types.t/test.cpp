struct C {
  struct {
    int x;
  } _a;
  struct {
    int x;
    int y;
  } _b;
};

int test() {
  C c;
  return c._a.x + c._b.x;
}
