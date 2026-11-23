// Compile-only inputs the proposed validator must reject. No validator exists yet.
// These functions are never called by the native runner.

// Trivial destruction is insufficient: x's lifetime ends at the goto.
// The original dereference is undefined; in-place suffix duplication makes it live.
// This is a safety-preservation obligation, not a native result comparison.
int escaped_scalar() {
    int *p;
    { int x = 1; p = &x; goto out; }
out:
    return *p;
}

// A textually forward edge can still lie on a cycle via a structured loop.
int forward_in_loop(int n) {
    int x = 0;
    while (x < n) {
        ++x;
        goto next;
        x += 100;
next:
        ;
    }
    return x;
}

// Legal C++, but an early edge adds a live variable, even without an initializer.
int skipped_vacuous_declaration(bool b) {
    if (b) goto out;
    int x;
    x = 1;
out:
    return 0;
}

// Labels can be entered from outside a loop, bypassing its condition.
int nested_target() {
    int x = 0;
    goto inside;
    while (false) {
inside:
        ++x;
    }
    return x;
}
