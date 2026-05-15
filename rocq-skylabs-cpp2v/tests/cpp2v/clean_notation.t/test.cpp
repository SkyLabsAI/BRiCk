enum : int { FOO = 3 };

template<typename T>
struct ID {
  using type = T;
};

template<typename T>
T id(typename ID<T>::type t) { return t; }

typename ID<decltype(FOO)>::type t = FOO;

struct Foo {
  int x;
  int y;
};

template<typename T>
struct Bar {
  T x;
};

Bar<int> b{1};
Bar<unsigned long long> c{3};

struct C {
  int x;
  struct {
    struct { int z; };
    int y;
  };
};
