namespace N {
inline constexpr auto first = [](auto value) { return value; };
using First = decltype(first);
}
namespace N {
inline constexpr auto second = [value = 3](auto other) { return value + other; };
using Second = decltype(second);
}
static_assert(sizeof(N::First) == 1);
static_assert(sizeof(N::Second) == sizeof(int));
