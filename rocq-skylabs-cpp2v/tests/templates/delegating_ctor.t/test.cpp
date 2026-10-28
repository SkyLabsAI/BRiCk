struct S {
  S(int) {}

  template<typename T>
  S(T) : S(0) {}
};
