// split_view over ref_view: same shape as transform_view.
#include <ranges>
#include <string>
int words(const std::string &s) { int k = 0; for (auto w : s | std::views::split(' ')) { (void)w; ++k; } return k; }
