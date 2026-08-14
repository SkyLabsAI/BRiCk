int add(int left, int right) { return left + right; }

int shape(int value) {
  int left = value, right = 2;
  if ((value > 0))
    return add(left, right);
  return 0;
}
