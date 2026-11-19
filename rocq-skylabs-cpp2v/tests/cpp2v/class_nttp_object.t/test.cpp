struct P {
    int a;
};

template <P p> int f() { return p.a; }

int g() { return f<P{3}>(); }
