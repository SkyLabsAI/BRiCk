struct C {
  int foo:3;
  int bar:4;
};

int test() {
  C c;
  return c.foo;
}
