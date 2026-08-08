enum Kind { KZero = 0, KOne };

struct Record {
  int field;

  int method(int x) const {
    if (x > 0)
      return field + x;
    return field;
  }
};

template <typename T> struct Box {
  T value;

  T get() const { return value; }
};

template <typename T> T twice(T x) { return x + x; }

int redeclared(int x);

int redeclared(int x) {
  Record value{x};
  return value.method(twice<int>(x));
}

template int twice<int>(int);
