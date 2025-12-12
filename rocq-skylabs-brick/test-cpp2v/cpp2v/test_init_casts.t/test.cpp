/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

struct C {};

const C mk_cc() { return C{}; }
C mk_c() { return C{}; }

void test() {
        C   x0  = C{};
  const C   x1{};
  const C   x2  = C{};
        C   x3  = mk_c();
  const C   x4  = mk_c(); // cast which adds const
        C   x5  = mk_cc(); // cast which removes const
  const C   x6  = mk_cc();
  const C   x7[2]{};
        C   x8[3];
  const C   x9[3];
  const C   x10[4]{mk_c(), // add-const
                   mk_cc(), // nothing
                   C{},     // 2 no-op casts (second is functional cast)
                   {}};     // initlist const
        C   x11[4]{mk_c(),  // nothing
                   mk_cc(), // remove-const
                   C{},     // no-op cast (functional cast expr)
                   {}};     // nothing


#if 0	// avoid scope extrusion error
  const C&  y7  = mk_c();
  const C&  y8  = mk_cc();
  const C&& y9  = mk_c();
  const C&& y10 = mk_cc();
#endif
}

struct DD {
  DD() {} // this forces the use of the constructor rather than initlist
  DD(const DD&) {}
  DD& operator=(DD&);
};

void test_ctor() {
        DD   x0  = DD{};
  const DD   x1  = DD{};

        DD   x2{};
  const DD   x3{};

        DD   x4[2]{};
  const DD   x5[2]{};

        DD   x6[3];
  const DD   x7[3];


  int n = 3;
        DD*  x8 = new DD[n]{};
  const DD*  x9 = new DD[n]{};

}

extern void foo(const C c, C cc);

void test2() {
  foo(mk_c(), // nothing
      mk_cc()); // remove const
  foo(mk_cc(), // remove const
      mk_c()); // nothing

}

struct D : public C {};

void test3() {
  D d;
  static_cast<void>(static_cast<C&>(d)); // derived2base cast
  C c;
  static_cast<void>(static_cast<D&>(c)); // base2derived cast
}

struct AA {
        DD d[3];
  const DD dd[3];
  AA(AA&) = default;
};
