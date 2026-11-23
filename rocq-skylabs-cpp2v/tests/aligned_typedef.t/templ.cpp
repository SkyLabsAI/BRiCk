// Packed fields of a record that is not a template, accessed from templates.
struct __attribute__((packed)) S {
    char c;
    float v;
    // A type-dependent assignment, and one that is not type-dependent.
    template <typename T> void set(const T &r) { v = r; }
    template <typename T> void set_float(T, float f) { v = f; }
    template <typename T> float get(T) const { return v; }
};
template <typename T> void set_free(S &s, const T &r) { s.v = r; }

void use(S &s) {
    s.set(1.0f);
    s.set_float(0, 2.0f);
    (void)s.get(0);
    set_free(s, 3.0f);
}
