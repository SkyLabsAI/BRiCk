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

// Updates, from templates.
struct __attribute__((packed)) P {
    char c;
    unsigned int n;
};
template <typename T> void bump(P &p, T k) {
    p.n += 1;
    p.n += k;
    ++p.n;
    p.n--;
}
void use_p(P &p) { bump(p, 2); }
