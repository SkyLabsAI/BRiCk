struct C {};
struct D {
  static void operator delete(void*) {}
};

void test(C* cp, D* dp) {
  delete cp;
  delete dp;
}

#if 0
#if __cplusplus >= 202002L
namespace std {
struct destroying_delete_t { explicit destroying_delete_t() = default; };
inline constexpr destroying_delete_t destroying_delete{};
};
struct E {
  static void operator delete(E* ptr, std::destroying_delete_t) {}
};
void test_destroying_delete(E* ep) {
  delete ep;
}
#else
#warning "C++ version is not compatible 2020"
#endif
#endif
