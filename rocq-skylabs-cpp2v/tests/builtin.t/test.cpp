void test() {
  int* pi;
  char* ci;


  __builtin_launder(pi);
  __builtin_launder(ci);

  __atomic_load_n(pi, __ATOMIC_SEQ_CST);
  __atomic_load_n(ci, __ATOMIC_SEQ_CST);
}
