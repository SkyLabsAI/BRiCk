// Named loops (C2y N3355, clang 22 `-fnamed-loops`): the target loop is not
// the innermost one. SkyLabsAI/BRiCk#540.
int named_break() {
  int r = 0;
outer:
  while (r == 0) {
    while (true) { break outer; }
    r = 1;
  }
  return r;
}
int named_continue() {
  int r = 0;
outer:
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 2; ++j) { continue outer; }
    r += 1;
  }
  return r;
}
// An unnamed break inside a labeled loop is an ordinary break.
int plain_break() {
outer:
  while (true) { break; }
  return 0;
}
