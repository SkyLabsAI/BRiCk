// Statement attributes that are promises to the compiler, which [Sattr]
// would drop. An assumption has undefined behaviour unless its expression
// holds, and the expression is not evaluated; [Ecall] would evaluate the
// builtin's. Each spelling prints unsupported.
int assume_attr(int x) { [[assume(x == 0)]]; return x; }
int assume_gnu_attr(int x) { __attribute__((assume(x == 0))); return x; }
int assume_builtin(int x) { __builtin_assume(x == 0); return x; }
// `assume_safety` promises that the loop has no loop-carried dependency.
void loop_assume_safety(int *a, int n) {
#pragma clang loop vectorize(assume_safety)
  for (int i = 1; i < n; i++) a[i] = a[i - 1] + 1;
}
// `musttail` ends the lifetime of the caller's locals before the call.
int callee(int *);
int musttail(int *p) { [[clang::musttail]] return callee(p); }
// Hints and diagnostics stay [Sattr]: this function is supported.
void hint(int);
int hints(int *a, int n) {
  if (n < 0) [[unlikely]] return 0; else [[likely]] hint(n);
  switch (n) { case 0: hint(0); [[fallthrough]]; default: break; }
#pragma clang loop vectorize(disable)
  for (int i = 1; i < n; i++) a[i] = a[i - 1] + 1;
#pragma unroll 4
  for (int i = 1; i < n; i++) a[i] = a[i - 1] + 1;
  [[clang::nomerge]] hint(1);
  [[clang::noinline]] hint(2);
  return n;
}
