// Parentheses around a builtin's name put a ParenExpr between the
// BuiltinFnToFnPtr cast and the DeclRefExpr.
int f() { return (__builtin_abs)(1); }
