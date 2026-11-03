template<class T> struct Box {
    T value = 0;
    bool engaged = false;
    int untouched;
};

// Instantiating the layout must not force an ill-formed, unused initializer.
struct NoIntConversion {};
static_assert(sizeof(Box<NoIntConversion>) > 0);
static_assert(sizeof(Box<unsigned long>) > 0);
