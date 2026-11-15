void shadowed() {
    bool t = true;
    for (int i = 0; bool t = (i++ < 3);) {}
}

void unshadowed() {
    for (int i = 0; bool t = (i++ < 3);) {}
}

void ordinary() {
    for (int i = 0; i < 3; ++i) {}
}
