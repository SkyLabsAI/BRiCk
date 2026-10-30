// Exercise the binding and lifetime of a declaration in a for condition.
int shadowed() {
    int value = 1;
    for (; int value = 0;) {}
    return value;
}

int unshadowed() {
    for (; int value = 0;) {}
    return 0;
}

int increment_binding() {
    int count = 0;
    for (; int step = count < 2; count += step) {
        continue;
    }
    return count;
}

int ordinary() {
    int sum = 0;
    for (int n = 0; n < 2; ++n) sum += n;
    return sum;
}

int events[64];
int event_count;
void record(int event) { events[event_count++] = event; }

struct Condition {
    int value;
    int limit;
    Condition(int value, int limit) : value(value), limit(limit) {
        record(100 + value);
    }
    explicit operator bool() const {
        record(200 + value);
        return value < limit;
    }
    ~Condition() { record(500 + value); }
};

struct Body {
    int value;
    explicit Body(int value) : value(value) { record(300 + value); }
    ~Body() { record(350 + value); }
};

int normal_and_continue() {
    int n = 0;
    for (record(1); Condition condition = Condition(n, 2);
         record(400 + condition.value), ++n) {
        Body local(condition.value);
        if (condition.value == 0) continue;
    }
    return n;
}

int break_cleanup() {
    int n = 0;
    for (record(1); Condition condition = Condition(n, 1);
         record(400 + condition.value), ++n) {
        Body local(condition.value);
        break;
    }
    return n;
}

int return_cleanup() {
    int n = 0;
    for (record(1); Condition condition = Condition(n, 1);
         record(400 + condition.value), ++n) {
        Body local(condition.value);
        return 42;
    }
    return -1;
}

int nested_continue() {
    int n = 0;
    for (; Condition condition = Condition(n, 1);
         record(400 + condition.value), ++n) {
        Body local(condition.value);
        for (int inner = 0; inner < 2; ++inner) {
            if (inner == 0) continue;
            record(600 + inner);
        }
    }
    return n;
}

#ifdef NATIVE_ORACLE
// The trace checks body cleanup before increment, condition cleanup after it,
// reconstruction before every test (including the false one), and no increment
// on break/return. The leading event also checks that the initializer runs once.
bool trace_matches(const int* expected, int count) {
    if (event_count != count) return false;
    for (int n = 0; n < count; ++n)
        if (events[n] != expected[n]) return false;
    return true;
}

int main() {
    if (shadowed() != 1 || unshadowed() != 0 || increment_binding() != 2 ||
        ordinary() != 1) return 1;
    event_count = 0;
    if (normal_and_continue() != 2) return 2;
    const int normal[] = {1, 100, 200, 300, 350, 400, 500,
                         101, 201, 301, 351, 401, 501, 102, 202, 502};
    if (!trace_matches(normal, 16)) return 3;
    event_count = 0;
    if (break_cleanup() != 0) return 4;
    const int abrupt[] = {1, 100, 200, 300, 350, 500};
    if (!trace_matches(abrupt, 6)) return 5;
    event_count = 0;
    if (return_cleanup() != 42) return 6;
    if (!trace_matches(abrupt, 6)) return 7;
    event_count = 0;
    if (nested_continue() != 1) return 8;
    const int nested[] = {100, 200, 300, 601, 350, 400, 500, 101, 201, 501};
    if (!trace_matches(nested, 10)) return 9;
}
#endif
