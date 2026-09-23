struct alignas(64) OverAligned {};

OverAligned *make_overaligned() {
    return new OverAligned;
}
