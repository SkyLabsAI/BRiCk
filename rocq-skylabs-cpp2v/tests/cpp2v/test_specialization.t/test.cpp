struct FD {
  FD() = delete;
  ~FD() = delete;
  FD(FD&) = delete;
  FD(FD&&) = delete;
    volatile void *_p{nullptr};
    template<typename T>
    explicit operator T() {
        return *(static_cast<volatile T *>(_p));
    }
};

template FD::operator char();
template FD::operator short();

template<typename T>
struct A {
  A() = delete;
  ~A() = delete;
  A(A&) = delete;
  A(A&&) = delete;
  template<typename U>
  explicit operator U() {
    return U{};
  }
  template<typename U>
  T test(U) { return U{}; }
};

template A<int>::operator char();
template A<bool>::operator long();

template int A<int>::test(char);
template bool A<bool>::test(long);
