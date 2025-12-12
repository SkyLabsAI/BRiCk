template<typename T>
struct is_int {
  static constexpr bool value = false;
};
template<>
struct is_int<int> {
  static constexpr bool value = true;
};

template<typename T>
void getIt() requires is_int<T>::value { }

template<typename T>
int getIt() requires (!is_int<T>::value) { return 1; }

void test() {
  getIt<int>();
  getIt<long>();
}
