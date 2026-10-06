template <class T> struct W {
  W() = default;
  W(const W &) { static_assert(sizeof(T) == 0, "W<T>::W(const W&) instantiated"); }
};
struct X { W<int> w; };
X make() { return X{}; }
