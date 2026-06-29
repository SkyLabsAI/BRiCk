#include <vector>

namespace test {
template <typename T>
class Matrix {
  std::vector<std::vector<T>> data;

public:
  template <typename Number>
  void use(Matrix<Number> const &other) const {}
};
} // namespace test

void test_add() {
  test::Matrix<int> x;
  test::Matrix<int> y;
  x.use(y);
}
