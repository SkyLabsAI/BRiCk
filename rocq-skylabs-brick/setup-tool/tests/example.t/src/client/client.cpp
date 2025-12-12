#include<util.hpp>
#include<client.hpp>

int main() {
  unsigned int i = 0;
  i = add_one(i);
  i = add_two(i);

  return (i == 3) ? 0 : 1;
}
