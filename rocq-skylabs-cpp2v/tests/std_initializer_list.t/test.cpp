#include <initializer_list>

// [dcl.init.list]#5 / clang's [CXXStdInitializerListExpr].
//
// The backing array of a <<std::initializer_list>> is a temporary. Where that
// temporary's lifetime ends with the enclosing full-expression, BRiCk supports
// the conversion; where it is lifetime-extended (a "scope-extruded temporary")
// it does not.

int sum(std::initializer_list<int> l) {
  int acc = 0;
  for (auto x : l)
    acc += x;
  return acc;
}

struct Widget {
  int a;
  int b;
};

struct Holder {
  int n;
  Holder(std::initializer_list<int> l) : n((int)l.size()) {}
};

// Supported: the backing array dies with the full-expression.
int pass_to_function() { return sum({1, 2, 3}); }

int copy_init_class() {
  Holder h = {1, 2, 3};
  return h.n;
}

int direct_init_class() {
  Holder h{1, 2, 3};
  return h.n;
}

int nested_elements() { return sum({1, 2, 3}) + sum({}); }

std::initializer_list<Widget> widgets() { return {{1, 2}, {3, 4}}; }

// Supported, but no [CXXStdInitializerListExpr]: clang uses the default
// constructor for an empty braced-init-list.
int empty_list() {
  std::initializer_list<int> l = {};
  return (int)l.size();
}

// Unsupported: the backing array is lifetime-extended to match <<l>>.
int extended_temporary() {
  std::initializer_list<int> l = {1, 2, 3};
  return (int)l.size();
}
