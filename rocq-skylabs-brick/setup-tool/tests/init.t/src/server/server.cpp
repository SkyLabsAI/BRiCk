#include<util.hpp>
#include<server.hpp>

int main() {
  unsigned int i = 0;
  i = add_one(i);
  i = add_three(i);

  return (i == 4) ? 0 : 1;
}
