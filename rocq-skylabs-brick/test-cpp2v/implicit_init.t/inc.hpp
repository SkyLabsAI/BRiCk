template<typename T, T v>
struct integral_constant {
  static constexpr T value = v;
};

template<bool B>
using bool_constant = integral_constant<bool, B>;

auto x = sizeof(integral_constant<bool, true>::value);
