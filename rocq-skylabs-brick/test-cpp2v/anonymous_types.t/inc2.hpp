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
