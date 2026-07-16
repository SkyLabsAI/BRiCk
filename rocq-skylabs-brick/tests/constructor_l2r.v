Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.typed.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{{
struct C {
  int data;
  C(int x):data(x) {}
};

struct D : C {
  int dd;
  using C::C;
};

struct VariadicBase {
  int data;
  VariadicBase(int x, ...):data(x) {}
};

struct VariadicDerived : VariadicBase {
  using VariadicBase::VariadicBase;
};

struct OverloadBase {
  int data;
  OverloadBase(int x):data(x) {}
  OverloadBase(int x, int y, ...):data(x + y) {}
};

struct OverloadDerived : OverloadBase {
  using OverloadBase::OverloadBase;
};

struct DefaultArgBase {
  int data;
  DefaultArgBase(int x, int y = 5):data(x + y) {}
};

struct DefaultArgDerived : DefaultArgBase {
  using DefaultArgBase::DefaultArgBase;
};

struct LeftBase {
  int left;
  LeftBase():left(0) {}
  LeftBase(int x):left(x) {}
};

struct RightBase {
  int right;
  RightBase():right(0) {}
  RightBase(char c):right(c) {}
};

struct MultipleDerived : LeftBase, RightBase {
  using LeftBase::LeftBase;
  using RightBase::RightBase;
};

struct MemberBase {
  int data;
  MemberBase(int x):data(x) {}
};

struct MemberDerived : MemberBase {
  int extra = 42;
  using MemberBase::MemberBase;
};

struct TemplateBase {
  int data;
  template <typename T>
  TemplateBase(T x):data(static_cast<int>(x)) {}
};

struct TemplateDerived : TemplateBase {
  using TemplateBase::TemplateBase;
};

struct PackBase {
  int count;
  template <typename... Ts>
  PackBase(int, Ts...):count(sizeof...(Ts)) {}
};

struct PackDerived : PackBase {
  using PackBase::PackBase;
};

struct DeletedBase {
  int data;
  DeletedBase(int) = delete;
  DeletedBase(long x):data(static_cast<int>(x)) {}
};

struct DeletedDerived : DeletedBase {
  using DeletedBase::DeletedBase;
};

struct PrivateBase {
  int data;
  PrivateBase(int x):data(x) {}
};

struct PrivateDerived : PrivateBase {
private:
  using PrivateBase::PrivateBase;

public:
  static PrivateDerived make(int x) {
    return PrivateDerived(x);
  }
};

void test() {
  D d(0);
  VariadicDerived vd0(1);
  VariadicDerived vd1(2, 3);
  VariadicDerived vd2(4, 5, 6);
  OverloadDerived od0(1);
  OverloadDerived od1(2, 3);
  OverloadDerived od2(4, 5, 6);
  DefaultArgDerived dad0(1);
  DefaultArgDerived dad1(2, 3);
  MultipleDerived md0(7);
  MultipleDerived md1('a');
  MemberDerived mem(8);
  TemplateDerived td0(9);
  TemplateDerived td1('b');
  PackDerived pd0(10);
  PackDerived pd1(11, 12);
  PackDerived pd2(13, 14, 15);
  DeletedDerived del(16L);
  PrivateDerived priv = PrivateDerived::make(17);
}
}}}.

Eval vm_compute in decltype.check_tu source.
