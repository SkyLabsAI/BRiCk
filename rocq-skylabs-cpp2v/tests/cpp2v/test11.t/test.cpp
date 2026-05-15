/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

int foo(int x[]) {
    return x[1];
}

class Box {
private:
    int value;
public:
    Box(int val):value(val) {}
    ~Box() {
    }
};


template<typename T>
class BoxT {
private:
    T value;
public:
    BoxT(T val):value(val) {}
    ~BoxT() {
        if (true)
            delete this;
    }
};


int m() {
    BoxT<int> a(1);
    return 0;
}
