/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

struct S {
    unsigned some_bit : 1;
    unsigned some_other_bit : 1;
};

unsigned read(const S &value) {
    return value.some_bit;
}

void write(S *value, unsigned bits) {
    value->some_bit = bits;
}

void update(S &value) {
    value.some_bit += 1;
    ++value.some_other_bit;
    value.some_bit++;
}

unsigned conditional(bool choose, S &left, S &right) {
    return choose ? left.some_bit : right.some_other_bit;
}

unsigned binding(S &value) {
    auto &[first, second] = value;
    first = 1;
    return second;
}

struct Anonymous {
    struct {
        unsigned bits : 1;
    };
};

unsigned indirect(Anonymous &value) {
    return value.bits;
}

template <unsigned Width> struct Sized {
    unsigned bits : Width;
};

unsigned specialized(Sized<3> &value) {
    return value.bits;
}
