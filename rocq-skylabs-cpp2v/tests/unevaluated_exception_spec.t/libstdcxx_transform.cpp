// transform_view() requires default_initializable<_Vp> = default; next to
// `_Vp _M_base = _Vp();` with _Vp = ref_view<...>, which has no default ctor.
#include <ranges>
#include <vector>
int sum(const std::vector<int> &v) {
  int s = 0;
  for (int x : v | std::views::transform([](int i) { return i * 2; })) s += x;
  return s;
}
