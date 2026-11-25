cpp2v must not evaluate an exception specification that clang left
unevaluated or uninstantiated: the translation unit does not need it, and
evaluating it can be ill-formed (issue #507).

  $ check_cpp2v default_member_init.cpp
  cpp2v -v -check-types -o default_member_init_17_cpp.v default_member_init.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix default_member_init_17_cpp.v
  $ check_cpp2v defaulted_copy_ctor.cpp
  cpp2v -v -check-types -o defaulted_copy_ctor_17_cpp.v defaulted_copy_ctor.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix defaulted_copy_ctor_17_cpp.v
  $ check_cpp2v defaulted_move_assign.cpp
  cpp2v -v -check-types -o defaulted_move_assign_17_cpp.v defaulted_move_assign.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix defaulted_move_assign_17_cpp.v
  $ check_cpp2v defaulted_dtor.cpp
  cpp2v -v -check-types -o defaulted_dtor_17_cpp.v defaulted_dtor.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix defaulted_dtor_17_cpp.v
  $ check_cpp2v user_dtor.cpp
  cpp2v -v -check-types -o user_dtor_17_cpp.v user_dtor.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix user_dtor_17_cpp.v
  $ check_cpp2v implicit_copy_ctor_template.cpp
  cpp2v -v -check-types -o implicit_copy_ctor_template_17_cpp.v implicit_copy_ctor_template.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix implicit_copy_ctor_template_17_cpp.v

C++20 defaulted comparison.

  $ check_cpp2v_versions defaulted_eq.cpp 20
  cpp2v -v -check-types -o defaulted_eq_20_cpp.v defaulted_eq.cpp -- -std=c++20 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix defaulted_eq_20_cpp.v

In a non-template class, elaboration defines the unused defaulted members, which
needs their exception specifications. So, by default, cpp2v still fails on
these; elaboration is out of scope here. Without elaboration, they succeed.

  $ check_cpp2v default_member_init_nontemplate.cpp
  cpp2v -v -check-types -o default_member_init_nontemplate_17_cpp.v default_member_init_nontemplate.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/default_member_init_nontemplate.cpp:3:88: error: no matching constructor for initialization of 'NoDefault'
  template <class T> struct Holder { Holder() = default; Holder(const T &v) : t(v) {} T t{}; };
                                                                                         ^~
  $TESTCASE_ROOT/default_member_init_nontemplate.cpp:3:36: note: in instantiation of default member initializer 'Holder<NoDefault>::t' requested here
  template <class T> struct Holder { Holder() = default; Holder(const T &v) : t(v) {} T t{}; };
                                     ^
  $TESTCASE_ROOT/default_member_init_nontemplate.cpp:4:30: note: in evaluation of exception specification for 'Holder<NoDefault>::Holder' needed here
  struct S { Holder<NoDefault> h; S() = default; S(int i) : h(NoDefault(i)) {} };
                               ^
  $TESTCASE_ROOT/default_member_init_nontemplate.cpp:4:33: note: in evaluation of exception specification for 'S::S' needed here
  struct S { Holder<NoDefault> h; S() = default; S(int i) : h(NoDefault(i)) {} };
                                  ^
  $TESTCASE_ROOT/common.hpp:6:20: note: candidate constructor not viable: requires 1 argument, but 0 were provided
  struct NoDefault { NoDefault(int) {} };
                     ^         ~~~
  $TESTCASE_ROOT/common.hpp:6:8: note: candidate constructor (the implicit copy constructor) not viable: requires 1 argument, but 0 were provided
  struct NoDefault { NoDefault(int) {} };
         ^~~~~~~~~
  $TESTCASE_ROOT/common.hpp:6:8: note: candidate constructor (the implicit move constructor) not viable: requires 1 argument, but 0 were provided
  struct NoDefault { NoDefault(int) {} };
         ^~~~~~~~~
  1 error generated.
  Error while processing $TESTCASE_ROOT/default_member_init_nontemplate.cpp.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix default_member_init_nontemplate_17_cpp.v
  Error: Can't find file ./default_member_init_nontemplate_17_cpp.v
  [1]
  $ check_cpp2v implicit_copy_ctor.cpp
  cpp2v -v -check-types -o implicit_copy_ctor_17_cpp.v implicit_copy_ctor.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  In file included from $TESTCASE_ROOT/implicit_copy_ctor.cpp:1:
  $TESTCASE_ROOT/common.hpp:10:28: error: no member named 'value' in 'Bad'
    W(const W &) noexcept(T::value) {}
                          ~~~^
  $TESTCASE_ROOT/implicit_copy_ctor.cpp:3:19: note: in instantiation of exception specification for 'W' requested here
  struct I { W<Bad> w; };
                    ^
  $TESTCASE_ROOT/implicit_copy_ctor.cpp:3:8: note: in evaluation of exception specification for 'I::I' needed here
  struct I { W<Bad> w; };
         ^
  In file included from $TESTCASE_ROOT/implicit_copy_ctor.cpp:1:
  $TESTCASE_ROOT/common.hpp:12:20: error: no member named 'value' in 'Bad'
    ~W() noexcept(T::value) {}
                  ~~~^
  $TESTCASE_ROOT/implicit_copy_ctor.cpp:3:8: note: in instantiation of exception specification for '~W' requested here
  struct I { W<Bad> w; };
         ^
  $TESTCASE_ROOT/implicit_copy_ctor.cpp:3:8: note: in implicit copy constructor for 'I' first required here
  In file included from $TESTCASE_ROOT/implicit_copy_ctor.cpp:1:
  $TESTCASE_ROOT/common.hpp:11:34: error: no member named 'value' in 'Bad'
    W &operator=(W &&) noexcept(T::value) { return *this; }
                                ~~~^
  $TESTCASE_ROOT/implicit_copy_ctor.cpp:3:19: note: in instantiation of exception specification for 'operator=' requested here
  struct I { W<Bad> w; };
                    ^
  $TESTCASE_ROOT/implicit_copy_ctor.cpp:3:8: note: in evaluation of exception specification for 'I::operator=' needed here
  struct I { W<Bad> w; };
         ^
  3 errors generated.
  Error while processing $TESTCASE_ROOT/implicit_copy_ctor.cpp.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix implicit_copy_ctor_17_cpp.v
  Error: Can't find file ./implicit_copy_ctor_17_cpp.v
  [1]
  $ CRAM_CPP2VFLAGS=--no-elaborate check_cpp2v default_member_init_nontemplate.cpp
  cpp2v -v -check-types -o default_member_init_nontemplate_17_cpp.v default_member_init_nontemplate.cpp --no-elaborate -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix default_member_init_nontemplate_17_cpp.v
  $ CRAM_CPP2VFLAGS=--no-elaborate check_cpp2v implicit_copy_ctor.cpp
  cpp2v -v -check-types -o implicit_copy_ctor_17_cpp.v implicit_copy_ctor.cpp --no-elaborate -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix implicit_copy_ctor_17_cpp.v

libstdc++. Only cpp2v is checked: the generated files are large, and `rocq c`
rejects them for unrelated reasons (x87 `long double`).

  $ for f in libstdcxx_transform libstdcxx_split libstdcxx_unordered_map_lambda_hash; do cpp2v_command -o $f.v $f.cpp -- -std=c++20 > /dev/null 2>&1 || echo "$f: failed"; done
