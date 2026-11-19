template <typename T> struct A {
    A() = default;

    template <typename U> static constexpr bool enabled = true;

    template <typename U>
        requires enabled<U>
    A(const A<U> &);
};

A<int> value;
