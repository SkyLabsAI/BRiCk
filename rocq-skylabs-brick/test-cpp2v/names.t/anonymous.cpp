struct C {
  struct {
    int x;
  } _a;
  struct {
    int x;
    int y;
  } _b;
};

struct D {
  union {
    struct {
      int x;
    } a;
    struct {
      int y;
    } b;
  };
};
