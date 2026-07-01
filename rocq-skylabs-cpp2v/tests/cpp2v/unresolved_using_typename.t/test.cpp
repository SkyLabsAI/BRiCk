template <typename T>
struct Base {
  using value_type = T;
};

template <typename T>
struct Derived : Base<T> {
  using typename Base<T>::value_type;
};
