#include <cassert>
#include <iostream>
#include <limits>

static int observed;
struct Guard { ~Guard() { observed += 10; } };

int original(bool fail) {
    Guard guard;
    int amount = 1;
    if (fail) goto cleanup;
    amount = 2;
cleanup:
    observed += amount;
    return observed;
}

int lowered(bool fail) {
    Guard guard;
    int amount = 1;
    if (fail) {
        observed += amount;
        return observed;
    }
    amount = 2;
    observed += amount;
    return observed;
}

int clamp_original(int x) {
    if (x < 0) goto neg;
    return x;
neg:
    return 0;
}
int clamp_lowered(int x) {
    if (x < 0) return 0;
    return x;
    return 0;
}

int main() {
    for (bool fail : {false, true}) {
        const int expected = fail ? 1 : 2;
        for (auto f : {original, lowered}) {
            observed = 0;
            assert(f(fail) == expected);
            assert(observed == expected + 10);
        }
    }
    for (int x : {std::numeric_limits<int>::min(), -1, 0, 1,
                  std::numeric_limits<int>::max()}) {
        assert(clamp_original(x) == (x < 0 ? 0 : x));
        assert(clamp_lowered(x) == clamp_original(x));
    }
    std::cout << "same-scope RAII and clamp: original/lowered results agree\n";
}
