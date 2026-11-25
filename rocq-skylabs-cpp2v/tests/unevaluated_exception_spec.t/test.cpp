// Issue #507: `Holder<NoDefault>()` is never used, so its exception
// specification is never needed; evaluating it would instantiate the
// ill-formed default member initializer `T t{}`. libstdc++'s
// `transform_view` over a `ref_view` has the same shape.
struct NoDefault {
    NoDefault(int) {}
};
template <class T> struct Holder {
    Holder() = default;
    Holder(const T &v) : t(v) {}
    T t{};
};
int f() {
    Holder<NoDefault> x(NoDefault(1));
    return 0;
}
