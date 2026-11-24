// `asm goto` can jump to its labels; plain GCC `asm` prints as [Sasm].
int asm_goto(int x) {
  asm goto("jmp %l0" :::: L);
  return 0;
L:
  return 1;
}
int asm_plain(int x) {
  int y;
  asm("mov %1, %0" : "=r"(y) : "r"(x));
  return y;
}
