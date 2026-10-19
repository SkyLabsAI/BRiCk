template<typename T>
concept is_int = __is_same(T, int);

bool resolved_true() { return is_int<int>; }
bool resolved_false() { return is_int<char>; }

template<typename T>
int choice() {
    if constexpr (is_int<T>) {
        return 7;
    } else {
        return 9;
    }
}

int true_case() { return choice<int>(); }
int false_case() { return choice<char>(); }
