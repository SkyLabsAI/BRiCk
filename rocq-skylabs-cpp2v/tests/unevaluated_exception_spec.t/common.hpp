// Every file here is valid C++ and never uses the special members or
// comparisons whose exception specification it exercises, so that
// specification is never needed ([except.spec]p13). W<Bad>'s members have a
// noexcept-specifier that is ill-formed but never instantiated; NoDefault has
// no default constructor.
struct NoDefault { NoDefault(int) {} };
struct Bad {};
template <class T> struct W {
  W() = default;
  W(const W &) noexcept(T::value) {}
  W &operator=(W &&) noexcept(T::value) { return *this; }
  ~W() noexcept(T::value) {}
  bool operator==(const W &) const noexcept(T::value) { return true; }
};
