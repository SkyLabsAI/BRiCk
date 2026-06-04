struct Pair {
  int first;
  int second;
};

int test_decompose_address() {
  Pair pair{1, 2};
  auto [first, second] = pair;
  int *ptr = &first;
  return *ptr + second;
}
