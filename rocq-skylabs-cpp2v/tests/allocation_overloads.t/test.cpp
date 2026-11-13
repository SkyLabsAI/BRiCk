struct B {
    virtual ~B() {}
};

void destroy(B *p) { delete p; }
