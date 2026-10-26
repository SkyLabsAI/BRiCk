namespace Test {
template<class T> struct Holder { static const T value; };
template<class T> const T Holder<T>::value = T(7);
int actual_value = Holder<int>::value;
template<class T> inline constexpr auto template_closure = [](auto other) { return other; };
auto actual_closure = template_closure<int>;
}
