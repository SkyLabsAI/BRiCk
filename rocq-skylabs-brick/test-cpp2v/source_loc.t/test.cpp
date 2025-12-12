void test() {
  (void)__builtin_LINE();
  (void)__builtin_COLUMN();
  (void)__builtin_FUNCTION();
  // (void)__builtin_FUNCSIG();
  (void)__builtin_FILE();
  // (void)__builtin_FILE_NAME(); not supported by clang16
  //  (void)__builtin_source_location();
}
