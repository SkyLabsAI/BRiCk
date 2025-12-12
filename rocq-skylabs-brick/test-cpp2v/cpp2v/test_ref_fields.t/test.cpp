struct T {
  int &x;
};

int test(T& t) {
  return t.x;
}
