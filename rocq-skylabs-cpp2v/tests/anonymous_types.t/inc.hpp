#pragma once
enum {
  A, B
};

decltype(A) test_inc() { return A; }

struct {
  int a;
} global;


int get1() { return global.a; }

extern "C" void foo();

namespace {
  void bar() {}
}


struct {
  struct {
    struct {
      struct {
        struct { int zz; };
      };
    };
  };
} z;

// Unnamed records and enumerations whose invented names collide.
struct collide_in_class {
  struct { int a; } *p1;
  struct { long a; } *p2;
};

inline int collide_in_function() {
  int r;
  { enum { E = 1 }; r = E; }
  { enum { E = 0 }; r += E; }
  { struct { int b; } x = {1}; r += x.b; }
  { struct { long b; } x = {2}; r += x.b; }
  return r;
}
