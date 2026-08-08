using Plain = int;

template <class T>
using Alias = T *;

template <class T>
T identity(T value) {
  return value;
}

static_assert(sizeof(int) >= 2, "supported target");

int phase5_function(int value) { return identity(value); }
