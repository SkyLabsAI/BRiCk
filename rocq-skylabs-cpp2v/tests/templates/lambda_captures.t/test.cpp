template<typename T>
int lambda_variable_captures(T input)
{
  int local = 3;
  int other = 4;

  auto by_copy = [local](int x) {
    return local + x;
  };
  auto by_ref = [&other](int x) {
    other += x;
    return other;
  };
  auto init_capture = [sum = local + other](int x) {
    return sum + x;
  };
  auto default_copy = [=](int x) {
    return local + other + x;
  };
  auto default_ref = [&](int x) {
    other += input;
    return other + x;
  };

  return local + other;
}

template<typename T>
struct LambdaCaptureOwner {
  int value;

  int member_captures(int delta) {
    auto explicit_this = [this, delta]() {
      return this->value + delta;
    };
    auto implicit_this = [=]() {
      return value + delta;
    };
    auto copy_this = [*this, delta]() {
      return value + delta;
    };

    return value + delta;
  }
};
