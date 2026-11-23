#include <cassert>
#include <iostream>

int observed;
struct Guard { ~Guard() { observed = 7; } };

int cleanup_original() {
  observed = 1;
  { Guard g; goto out; }
out:
  return observed;
}
int cleanup_naive() {
  observed = 1;
  { Guard g; return observed; }
  return observed;
}

int shadow_original() {
  int x = 1;
  { int x = 2; (void)x; goto out; }
out:
  return x;
}
int shadow_naive() {
  int x = 1;
  { int x = 2; return x; }
  return x;
}

int continuation_original(bool c) {
  int x = 0;
  if (c) goto out;
  ++x;
out:
  ++x;
  return x;
}
int continuation_naive(bool c) {
  int x = 0;
  if (c) { ++x; }
  ++x;
  ++x;
  return x;
}

// All goto edges are textually forward, yet the CFG has a cycle.
int forward_inside_loop() {
  int x = 0;
  while (x < 3) {
    ++x;
    goto next;
    x += 100;
next:
    ;
  }
  return x;
}

int main() {
  const int co = cleanup_original(), cn = cleanup_naive();
  const int so = shadow_original(), sn = shadow_naive();
  const int to = continuation_original(true), tn = continuation_naive(true);
  std::cout << "cleanup: original=" << co << " naive=" << cn << '\n';
  std::cout << "shadow: original=" << so << " naive=" << sn << '\n';
  std::cout << "continuation(true): original=" << to << " naive=" << tn << '\n';
  std::cout << "forward_inside_loop=" << forward_inside_loop() << '\n';
  assert(co == 7 && cn == 1);
  assert(so == 1 && sn == 2);
  assert(to == 1 && tn == 3);
  assert(forward_inside_loop() == 3);
}
