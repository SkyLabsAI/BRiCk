// `this` in an unevaluated operand does not need a capture, so the lambda
// class has no `this` field.
struct S {
    void f() {
        [] { (void)sizeof(this); }();
    }
};
