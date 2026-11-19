// A case label under an `if`, as in decoder state machines and Duff's device.
int f(int state, int x) {
    switch (state) {
    case 0:
        if (x)
    case 1:
            return 1;
    }
    return 0;
}
