template <class T> struct M {
  M(int = T::nope) {}
};
struct X { M<int> m; };
