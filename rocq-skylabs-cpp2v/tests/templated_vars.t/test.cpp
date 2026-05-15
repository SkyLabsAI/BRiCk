template<typename T>
struct ID {
  using type = T;
  static const type max = 77;
};

template<typename T>
const T ID<T>::max;

template<typename T>
const decltype(sizeof(int)) bitsize = 8 * sizeof(T);

auto test() {
  return ID<int>::max; // + ID<short>::max;
}
