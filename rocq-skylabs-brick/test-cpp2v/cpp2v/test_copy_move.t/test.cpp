struct C {
  int x;
  C& operator=(const C&other) {
    x = other.x;
    return *this;
  }

};

struct D : C {
  int y;
};

void test() {
  D d;
  // D d_move = static_cast<D&&>(d);
  //  D d_copy = static_cast<D&>(d);

  // d_move = static_cast<D&&>(d);
  //  d_copy = d;
}
