// Hidden VLA bounds are anonymous fields, not named variable captures.
void plain(int n, int m) {
  int a[n];
  int b[m];
  auto lambda = [&] { return sizeof(a) + sizeof(b); };
}
