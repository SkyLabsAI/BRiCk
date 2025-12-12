/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
void* operator new(unsigned long) {
    static char buf[10];
    return buf;
}
void* operator new(unsigned long, void* p) {
    return p;
}

struct C {
    int x;
    C():x{0} {}
    C(int y):x(y) {}
};

struct X {
  void* operator new(unsigned long) noexcept {
    return nullptr;
  }
};

C* test(C* p) {
    auto z = new int();  // None None (Some (Eimplicit_init ..))
    auto y = new int{};  // None None (Some (Einit_list ..))
    auto zz = new int[15]; // None (Some 15) None
    auto zzz = new int[15](); // None (Some 15) (Some (Eimplicit_init ..))
    auto zzzz = new int[15]{1,2,3}; // None (Some 15) (Some (Einitlist ..))
    auto zzzzz = new C[2] {C(1), C(2)}; // None (Some 2) ...
    delete z;
    delete[] zz;
    p = new (p) C(3); // (Some placement_new) None (Some ctor)
    C* x = new C[10]; // None (Some 10) (Some ctor)
    delete[] x;
    delete p;
    new X();
    return new C(5);  // None None (Some ctor)
}


