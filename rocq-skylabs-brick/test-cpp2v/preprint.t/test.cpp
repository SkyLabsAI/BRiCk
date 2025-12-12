#include <iostream>
#include <vector>
#include <list>

using namespace std;

void test() {
  std::vector<int> a;
  std::list<std::vector<int> > v;
  v.push_back(a);
}
