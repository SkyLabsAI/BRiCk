// A lambda parameter's default argument names an enclosing local. With a
// capture-default, clang marks that DeclRefExpr as referring to an enclosing
// variable. The default argument is printed at the call site in `f`, which is
// not inside the lambda's call operator.
void f() {
    int x;
    [&](int = sizeof(x)) {}();
}
