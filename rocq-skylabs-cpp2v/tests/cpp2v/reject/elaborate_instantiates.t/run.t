Valid programs that [--elaborate] rejects: it defines members the program
never odr-uses ([dcl.fct.def.default]/5), instantiating ill-formed templates.

[X] is never copied, so [W<int>]'s copy constructor is not needed ([temp.inst]/4).

  $ check_cpp2v body.cpp
  cpp2v -v -check-types -o body_17_cpp.v body.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/body.cpp:3:32: error: static assertion failed due to requirement 'sizeof(int) == 0': W<T>::W(const W&) instantiated
    W(const W &) { static_assert(sizeof(T) == 0, "W<T>::W(const W&) instantiated"); }
                                 ^~~~~~~~~~~~~~
  $TESTCASE_ROOT/body.cpp:5:8: note: in instantiation of member function 'W<int>::W' requested here
  struct X { W<int> w; };
         ^
  $TESTCASE_ROOT/body.cpp:3:42: note: expression evaluates to '4 == 0'
    W(const W &) { static_assert(sizeof(T) == 0, "W<T>::W(const W&) instantiated"); }
                                 ~~~~~~~~~~^~~~
  1 error generated.
  Error while processing $TESTCASE_ROOT/body.cpp.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix body_17_cpp.v
  Error: Can't find file ./body_17_cpp.v
  [1]
  $ CRAM_CPP2VFLAGS=--no-elaborate check_cpp2v body.cpp
  cpp2v -v -check-types -o body_17_cpp.v body.cpp --no-elaborate -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix body_17_cpp.v

[X] is never default-constructed, so [M<int>]'s default argument is not
needed ([temp.inst]/14).

  $ check_cpp2v default_arg.cpp
  cpp2v -v -check-types -o default_arg_17_cpp.v default_arg.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/default_arg.cpp:2:11: error: type 'int' cannot be used prior to '::' because it has no members
    M(int = T::nope) {}
            ^
  $TESTCASE_ROOT/default_arg.cpp:4:8: note: in instantiation of default function argument expression for 'M<int>' required here
  struct X { M<int> m; };
         ^
  $TESTCASE_ROOT/default_arg.cpp:4:8: note: in implicit default constructor for 'X' first required here
  1 error generated.
  Error while processing $TESTCASE_ROOT/default_arg.cpp.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix default_arg_17_cpp.v
  Error: Can't find file ./default_arg_17_cpp.v
  [1]
  $ CRAM_CPP2VFLAGS=--no-elaborate check_cpp2v default_arg.cpp
  cpp2v -v -check-types -o default_arg_17_cpp.v default_arg.cpp --no-elaborate -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix default_arg_17_cpp.v
