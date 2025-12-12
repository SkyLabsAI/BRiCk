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
