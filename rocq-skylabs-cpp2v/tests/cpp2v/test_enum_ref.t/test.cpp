enum E : int {
  A = 0,
  B = A /* A here has type `int` */ + 1
};

void test() {
  A; // A here has type `E`
}
