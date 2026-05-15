namespace XXX {

  extern "C++" {
    int foo() { return 0; }
  }
  extern "C" {
    int bar() { return 1; }
  }

  extern int x;
  int y;

  int test() {
    extern int x;
    return x;
  }
}
