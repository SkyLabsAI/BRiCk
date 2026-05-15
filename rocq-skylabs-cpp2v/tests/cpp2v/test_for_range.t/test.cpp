/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

class Range {
public:
    class iterator {
    private:
        int val;
    public:
        iterator(int v):val(v) {}

        bool operator!=(const iterator& other) const {
            return val != other.val;
        }

        int operator*() const {
            return val;
        }

        iterator& operator++() {
            val++;
            return *this;
        }
    };

    iterator begin() const { return iterator(low); }
    iterator end() const { return iterator(high + 1); }

    Range(int l, int h):low(l),high(h) {}

private:
    int low, high;
};

void test() {
    Range r(0, 10);
    int x = 10;

    for (auto i : r) {
        x--;
    }

    for (const auto z = r; auto i : z) {
      x++;
    }


}
