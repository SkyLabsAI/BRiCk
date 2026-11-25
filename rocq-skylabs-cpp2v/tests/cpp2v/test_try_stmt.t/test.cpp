/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 *
 * SPDX-License-Identifier: MIT-0
 */

// Each `try` function below has a reference twin without `try`: cpp2v lowers
// `try B catch ... H` to `B`, so `test.v` checks that the two bodies are equal.

// A catch-all handler.
int try_add_one(int x) {
    int y = 0;
    try {
        y = x + 1;
    } catch (...) {
        y = -1;
    }
    return y;
}

int ref_add_one(int x) {
    int y = 0;
    {
        y = x + 1;
    }
    return y;
}

// Several handlers, including ones that bind the exception.
int try_typed_handlers(int x) {
    int y = 0;
    try {
        y = x * 2;
    } catch (int e) {
        y = e;
    } catch (const char *) {
        y = -2;
    } catch (...) {
        y = -1;
    }
    return y;
}

int ref_typed_handlers(int x) {
    int y = 0;
    {
        y = x * 2;
    }
    return y;
}

// Nested `try` statements, in the try-block and in a handler.
int try_nested(int x) {
    int y = 0;
    try {
        try {
            y = x + 1;
        } catch (...) {
            y = -1;
        }
        y = y + 1;
    } catch (...) {
        try {
            y = -2;
        } catch (...) {
            y = -3;
        }
    }
    return y;
}

int ref_nested(int x) {
    int y = 0;
    {
        {
            y = x + 1;
        }
        y = y + 1;
    }
    return y;
}

// Control flow leaving the try-block.
int try_control_flow(int n) {
    int sum = 0;
    for (int i = 0; i < n; ++i) {
        try {
            if (i == 3)
                continue;
            if (i == 5)
                break;
            if (i == 7)
                return -1;
            sum += i;
        } catch (...) {
            return -2;
        }
    }
    return sum;
}

int ref_control_flow(int n) {
    int sum = 0;
    for (int i = 0; i < n; ++i) {
        {
            if (i == 3)
                continue;
            if (i == 5)
                break;
            if (i == 7)
                return -1;
            sum += i;
        }
    }
    return sum;
}

// A `throw` inside the try-block stays unsupported (no WP rule), so dropping
// the handler that would catch it does not make the function verifiable.
int try_throw(int x) {
    try {
        if (x < 0)
            throw x;
        return x;
    } catch (int e) {
        return -e;
    }
}

int ref_throw(int x) {
    {
        if (x < 0)
            throw x;
        return x;
    }
}

// A function-try-block.
int try_function_block(int x) try {
    return x + 1;
} catch (...) {
    return -1;
}

int ref_function_block(int x) {
    return x + 1;
}

// A constructor function-try-block keeps its member initializers. (Its
// handler may not use members, and rethrows when it finishes.)
struct S {
    int v;
    S(int x) try : v(x) {
        v += 1;
    } catch (...) {
    }
    S(int x, long) : v(x) {
        v += 1;
    }
};

void use_s() {
    S a(1);
    S b(1, 2L);
}
