// A capturing lambda has no default ctor; reached via _Hashtable_ebo_helper.
#include <unordered_map>
int g(int salt) {
  auto h = [salt](int k) { return std::hash<int>{}(k ^ salt); };
  std::unordered_map<int, int, decltype(h)> m(8, h);
  m[1] = 2; return m[1];
}
