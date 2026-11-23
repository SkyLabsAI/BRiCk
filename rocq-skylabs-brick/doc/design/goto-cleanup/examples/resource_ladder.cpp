// Adapted from https://stackoverflow.com/a/70446256 by KamilCuk/community.
// Retrieved 2026-11-23; CC BY-SA 4.0, including these adaptations:
// https://creativecommons.org/licenses/by-sa/4.0/
// Codex changes: valid C++ spelling, hand-lowered comparison, trace harness.
#include "resource_api.h"
#include <cassert>
#include <iostream>
#include <vector>

static unsigned choices;
static int acquisitions;
static std::vector<int> events;
handle_t getResource() {
    const int n = ++acquisitions;
    events.push_back(10 + n);
    return choices & (1u << (n - 1)) ? n : 0;
}
void freeResource(handle_t h) {
    assert(h == 1 || h == 2);
    events.push_back(40 + h);
}
int action1(handle_t a, handle_t b) {
    assert(a == 1 && b == 2);
    events.push_back(31);
    return choices & 4u ? 11 : 0;
}
int action2(handle_t a, handle_t b) {
    assert(a == 1 && b == 2);
    events.push_back(32);
    return choices & 8u ? 12 : 0;
}

// Positive design example. The scalar handle exists before every goto.
int cpp_ladder() {
    int errorcode = 0;
    handle_t res1 = getResource();
    handle_t res2 = 0;
    if (!res1) {
        errorcode = somethnig;
        goto res1_fail;
    }
    res2 = getResource();
    if (!res2) {
        errorcode = somethnig_else;
        goto res2_fail;
    }
    errorcode = action1(res1, res2);
    if (!errorcode) goto actions_fail;
    errorcode = action2(res1, res2);
    if (!errorcode) goto actions_fail;
actions_fail:
    freeResource(res2);
res2_fail:
    freeResource(res1);
res1_fail:
    return errorcode;
}

// Proposed output, written manually; there is no implemented normalizer.
int lowered_ladder() {
    int errorcode = 0;
    handle_t res1 = getResource();
    handle_t res2 = 0;
    if (!res1) {
        errorcode = somethnig;
        return errorcode;
    }
    res2 = getResource();
    if (!res2) {
        errorcode = somethnig_else;
        freeResource(res1);
        return errorcode;
    }
    errorcode = action1(res1, res2);
    if (!errorcode) {
        freeResource(res2);
        freeResource(res1);
        return errorcode;
    }
    errorcode = action2(res1, res2);
    if (!errorcode) {
        freeResource(res2);
        freeResource(res1);
        return errorcode;
    }
    freeResource(res2);
    freeResource(res1);
    return errorcode;
}

static int run(int (*f)(), unsigned bits) {
    choices = bits;
    acquisitions = 0;
    events.clear();
    return f();
}

int main() {
    for (unsigned bits = 0; bits != 16; ++bits) {
        const int expected = !(bits & 1) ? somethnig :
            !(bits & 2) ? somethnig_else :
            !(bits & 4) ? 0 : (bits & 8) ? 12 : 0;
        std::vector<int> expected_events{11};
        if (bits & 1) {
            expected_events.push_back(12);
            if (bits & 2) {
                expected_events.push_back(31);
                if (bits & 4) expected_events.push_back(32);
                expected_events.push_back(42);
            }
            expected_events.push_back(41);
        }
        for (auto f : {somefunction, cpp_ladder, lowered_ladder}) {
            assert(run(f, bits) == expected);
            assert(events == expected_events);
        }
    }
    std::cout << "resource ladder: 16 choices, all 3 versions match return and trace\n";
}
