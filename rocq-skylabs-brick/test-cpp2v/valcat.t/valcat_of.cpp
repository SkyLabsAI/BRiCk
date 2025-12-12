/*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

struct C {
  int x{0};
  int a[10];
  int& r = x;
  int&& rr{static_cast<int&&>(x)};
  C& operator=(C&) { return *this; }
  C& operator=(C&&) { return *this; }
  C(const C&) {}
  C(C&&) {}
  C() {}
};

using FP = int (*)();

FP get_fp();
FP& get_fpl();
FP&& get_fpx();

// note, we use `sizeof` simply to get the type written into the AST.
#define CHECK_VALCAT(e) ((void)(e)) , sizeof(decltype((e)))

template<typename TY>
struct remove_reference { using result = TY; };
template<typename TY>
struct remove_reference<TY&> { using result = TY; };
template<typename TY>
struct remove_reference<TY&&> { using result = TY; };

template<typename T>
typename remove_reference<T>::result&& move(T& r) { return static_cast<typename remove_reference<T>::result &&>(r); }

void test() {
  C c;
  CHECK_VALCAT(1);
  CHECK_VALCAT(c);
  CHECK_VALCAT(static_cast<C&&>(c));
  CHECK_VALCAT(static_cast<C&>(c));
  CHECK_VALCAT(static_cast<C>(c));
  CHECK_VALCAT(static_cast<const C>(c));
  CHECK_VALCAT(static_cast<int>(1));
  CHECK_VALCAT(static_cast<const int>(2));

  CHECK_VALCAT(C().x);
  CHECK_VALCAT(c.x);
  CHECK_VALCAT(c.a[3]);
  CHECK_VALCAT(C().a[3]);
  CHECK_VALCAT(c.a);
  CHECK_VALCAT(c.a + 7);
  CHECK_VALCAT(C().a + 7);
  int x[10];
  CHECK_VALCAT(x[3]);
  CHECK_VALCAT(3[x]);
  CHECK_VALCAT(3[C().a]);
  CHECK_VALCAT(3[c.a]);
  CHECK_VALCAT(*x);
  CHECK_VALCAT(*c.a);
  CHECK_VALCAT(&c);
  CHECK_VALCAT(*C().a);
  CHECK_VALCAT(true && false);
  CHECK_VALCAT(true);
  CHECK_VALCAT("hello");
  CHECK_VALCAT(move(c));
  CHECK_VALCAT(move<C&>(c));
  CHECK_VALCAT(move<C&&>(c));
  CHECK_VALCAT(((void)1, c));
  CHECK_VALCAT(((void)c, 1));
  CHECK_VALCAT(true ? c : C());
  CHECK_VALCAT(true ? C() : c);
  CHECK_VALCAT(c.r);
  CHECK_VALCAT(C().r);
  CHECK_VALCAT(c.rr);
  CHECK_VALCAT(C().rr);
  CHECK_VALCAT(static_cast<C&&>(c).r);
  CHECK_VALCAT(static_cast<C&&>(c).rr);
  CHECK_VALCAT(static_cast<C&&>(c).x);
  CHECK_VALCAT(static_cast<C&>(c).r);
  CHECK_VALCAT(static_cast<C&>(c).rr);
  CHECK_VALCAT(static_cast<C&>(c).x);
  CHECK_VALCAT(static_cast<C>(c).r);
  CHECK_VALCAT(static_cast<C>(c).rr);
  CHECK_VALCAT(static_cast<C>(c).x);
  CHECK_VALCAT(static_cast<const C>(c).r);
  CHECK_VALCAT(static_cast<const C>(c).rr);
  CHECK_VALCAT(static_cast<const C>(c).x);
  CHECK_VALCAT(c = c);
  CHECK_VALCAT(x[3] = 3);
  CHECK_VALCAT(x[3] = 3);
  CHECK_VALCAT(x[3] |= 3);
  CHECK_VALCAT(c.a[9] &= 12);
  CHECK_VALCAT(static_cast<int*const&&>(x));
  CHECK_VALCAT(static_cast<int*const&>(x));
  CHECK_VALCAT(static_cast<int*const>(x));

  int y;
  CHECK_VALCAT(++static_cast<int&>(y));
  CHECK_VALCAT(--static_cast<int&>(y));
  CHECK_VALCAT(static_cast<int&>(y)++);
  CHECK_VALCAT(static_cast<int&>(y)--);

  int (*fp_prvalue)();
  CHECK_VALCAT((*fp_prvalue)());
  CHECK_VALCAT(fp_prvalue());

  int& (*fp_lvalue)();
  CHECK_VALCAT((*fp_lvalue)());
  CHECK_VALCAT(fp_lvalue());

  int&& (*fp_xvalue)();
  CHECK_VALCAT((*fp_xvalue)());
  CHECK_VALCAT(fp_xvalue());

  CHECK_VALCAT((get_fp())());
  CHECK_VALCAT((get_fpl())());
  CHECK_VALCAT((get_fpx())());
}
