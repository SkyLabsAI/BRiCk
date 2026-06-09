template<typename... T>
int sum(T... args) {
  auto count = sizeof...(T) + sizeof...(args);
  return static_cast<int>(count) + (args + ...);
}

void test() {
  (void)sum(1, 2ul, 3ll);
}
