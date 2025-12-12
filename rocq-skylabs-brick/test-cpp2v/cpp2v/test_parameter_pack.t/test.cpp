template<typename... T>
int sum(T... args) {
  return (args + ...);
}

void test() {
  (void)sum(1, 2ul, 3ll);
}
