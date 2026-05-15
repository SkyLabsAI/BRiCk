#include <utility>

void test()
{
  using namespace std;

  {
    auto p = pair<int,int>(1,2);
    auto &[x,y] = p;
    (void)(x + y);
  }

  {
    auto p = pair<int,int>(1,2);
    auto &&[x,y] = p;
    (void)(x + y);
  }

}
