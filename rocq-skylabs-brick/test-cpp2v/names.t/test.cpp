template<typename T1, typename T2>
static T1 run(T1 x, T2 v) {
  auto go = []<typename U>(U x, T1, T2) { return x; };
  return go((long)x, x, v);
}

// template<typename... XS>
// int foo(int x, XS&... xs) {
//   return x;
// }

template<typename T>
struct remove_reference_t {
  using type = T;
};
template<typename T>
struct remove_reference_t<T&> {
  using type = T;
};
template<typename T>
struct remove_reference_t<T&&> {
  using type = T;
};
template<typename T>
using remove_reference = typename remove_reference_t<T>::type;

template<typename T>
remove_reference<T>&& move(T&& x) noexcept {
  return static_cast<remove_reference<T>&&>(x);
}

template<>
int&& move(int&& x) noexcept { return static_cast<int&&>(x); }

template<typename U>
struct C {};

template<typename T>
void demo(const C<T>& x) { }

void test() {
  run(3, nullptr);

  auto x = 1;
  auto y = nullptr;
  auto z = true;
  // foo(3, x, y, z);

  move(x);
  move(y);
  move(z);

  C<char> c;
  demo(c);
}
