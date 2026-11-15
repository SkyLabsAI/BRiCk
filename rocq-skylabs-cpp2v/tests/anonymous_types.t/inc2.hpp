#pragma once
enum {
  C, D
};
decltype(C) test_inc2() { return C; }

struct {
  int a;
} global2;

int get2() { return global2.a; }

namespace {
  void bar2() {}
}

struct {
  struct {
    struct {
      struct {
        struct { int zz; };
      };
    };
  };
} y;

// Unnamed records whose invented names collide in a namespace.
namespace collide_ns {
  struct { int a; } *p3;
  struct { long a; } *p4;
}
