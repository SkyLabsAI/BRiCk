// A record with a non-empty base. Kept apart from test.cpp because the
// type checker run by --check-types does not support the derived-to-base
// casts in the implicit members of an opaque record.

struct B {
    int a : 3;
};

struct D : B {
    int f : 3;  // run "f": unsupported, it may continue a run of the base
    int sep;
    int g : 2;  // run "g": supported
};
