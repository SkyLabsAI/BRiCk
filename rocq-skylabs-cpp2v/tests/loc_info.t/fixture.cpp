#include "included.hpp"

struct pair_value {
    int first;
    int second;
};

template <typename T> T template_identity(T value) {
    T copy = value;
    return copy;
}

template <typename T> int dependent_location(T value) {
    return T::location_member(value);
}

int ordinary_location(int input) {
    auto [left, right] = pair_value{input, input};
    int result = HEADER_PLUS_ONE(input);
    return result + left + right;
}

int classify(int value) {
    switch (value) {
    case 0: {
        int copy = value;
        return copy;
    }
    case 1:
    default:
        return 2;
    }
}

template int template_identity<int>(int);
