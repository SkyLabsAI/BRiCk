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
needs their exception specifications; elaboration is out of scope here.

  $ CRAM_CPP2VFLAGS=--no-elaborate check_cpp2v default_member_init_nontemplate.cpp
  cpp2v -v -check-types -o default_member_init_nontemplate_17_cpp.v default_member_init_nontemplate.cpp --no-elaborate -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix default_member_init_nontemplate_17_cpp.v
  $ CRAM_CPP2VFLAGS=--no-elaborate check_cpp2v implicit_copy_ctor.cpp
  cpp2v -v -check-types -o implicit_copy_ctor_17_cpp.v implicit_copy_ctor.cpp --no-elaborate -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix implicit_copy_ctor_17_cpp.v

libstdc++. Only cpp2v is checked: the generated files are large, and `rocq c`
rejects them for unrelated reasons (x87 `long double`).

  $ for f in libstdcxx_transform libstdcxx_split libstdcxx_unordered_map_lambda_hash; do cpp2v_command -o $f.v $f.cpp -- -std=c++20 > /dev/null 2>&1 || echo "$f: failed"; done
