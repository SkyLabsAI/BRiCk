namespace cxx {
template<typename T>
T&& move(T& value);
}

void foo() {}

template<typename T>
struct Pair {
  T first;

  Pair(Pair&& pair) {
    ::foo();
    first = ::cxx::move(pair.first);
  }
};
