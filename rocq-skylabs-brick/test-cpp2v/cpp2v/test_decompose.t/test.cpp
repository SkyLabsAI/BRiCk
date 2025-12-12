#include <utility>

void test_pair() {
  std::pair<int,int> x{0,0};
  auto [a,b] = x;
  auto [aa,bb] = std::pair<int,std::pair<int,int> >{0,x};
  const auto [aa1,bb1] = std::pair<int,std::pair<int,int> >{0,x};

  auto& [aaa,bbb] = x;
  const auto& [xxx,yyy] = x;

  auto&& [aaar,bbbr] = static_cast<std::pair<int,int>&&>(x);
  const auto&& [xxxr,yyyr] = static_cast<std::pair<int,int>&&>(x);
}

int test_array()  {
  int ary[] = {1,2};
  auto [a,b] = ary;
  auto& [w,x] = ary;
  auto&& [t,u] = ary;

  return a + w + t;

}


void test_struct() {
  struct C { int x; char y; };

  C c;
  auto [a,b] = c;
  auto& [w,x] = c;
  auto&& [t,u] = c;
}
