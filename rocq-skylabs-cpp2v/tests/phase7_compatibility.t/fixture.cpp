template <typename T> auto dependent_decomposition(T value) {
    auto [left, right] = value;
    return left;
}

template <typename T> auto dependent_lambda(T value) {
    return []<typename U>(U inner) { return inner; }(value);
}

template <typename... Ts> int dependent_deduced_array() {
    constexpr int values[] = {sizeof(Ts)...};
    return values[0];
}

void *operator new(unsigned long, int *);
void *operator new(unsigned long, long *);
void *operator new[](unsigned long, int *);
void *operator new[](unsigned long, long *);
void operator delete(void *) noexcept;
void operator delete[](void *) noexcept;

template <typename T> void dependent_allocation_operators(T *pointer) {
    (void)::operator new(sizeof(T), pointer);
    (void)::operator new[](sizeof(T), pointer);
    ::operator delete(pointer);
    ::operator delete[](pointer);
}

template <typename T> struct DependentDispatch {
    using EntryPoint = int (*)(T);
    static int invoke(T);
    static EntryPoint mutableDispatch[1];
    static constexpr EntryPoint dispatch[] = {invoke};

    int runResolved(T value) { return mutableDispatch[0](value); }
    int runUnresolved(T value) { return dispatch[0](value); }
};

struct Pair {
    int left;
    int right;
};

int ordinary_decomposition(Pair value) {
    auto [left, right] = value;
    return left + right;
}

int instantiate_all(Pair value) {
    return dependent_decomposition(value) + dependent_lambda(1) +
           dependent_deduced_array<int, long>();
}
