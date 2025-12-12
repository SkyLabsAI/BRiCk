struct C { int x; };
void test() {
  C c;
  (void)static_cast<C&&>(c).x; // this should be an xvalue
}
