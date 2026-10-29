// Template lambda capture expressions must include Eunsupported's type.
template<class T> void templated(int n, int m) {
  int a[n];
  int b[m];
  auto lambda = [&] { return sizeof(a) + sizeof(b); };
}
