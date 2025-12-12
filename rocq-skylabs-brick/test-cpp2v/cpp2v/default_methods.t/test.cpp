template<typename T>
struct C {
  C<T>& operator=(C<T>&) = default;
};


void test() {
  C<int> c;
  c = c;
}
