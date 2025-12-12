struct C {};

int test() {
#if __is_identifier(__datasizeof)
  return 0;
#else
  return __datasizeof(struct C);
#endif
}
