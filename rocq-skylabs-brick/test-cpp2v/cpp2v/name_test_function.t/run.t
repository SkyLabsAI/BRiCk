  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bluerock.lang.cpp.mparser.
  
  #[local] Open Scope pstring_scope.
  
  Definition module_names : list Mname :=
    (
      (* Function fid() at $TESTCASE_ROOT/test.cpp:9:1 *) (Nglobal (Nfunction function_qualifiers.N "fid" nil)) ::
  
      (* CXXConstructor fname::fname() at $TESTCASE_ROOT/test.cpp:11:5 *) (Nscoped (Nglobal (Nid "fname")) (Nctor nil)) ::
  
      (* CXXDestructor fname::~fname() at $TESTCASE_ROOT/test.cpp:12:5 *) (Nscoped (Nglobal (Nid "fname")) Ndtor) ::
  
      (* CXXMethod fname::operator++() at $TESTCASE_ROOT/test.cpp:17:5 *) (Nscoped (Nglobal (Nid "fname")) (Nop function_qualifiers.N OOPlusPlus nil)) ::
  
      (* CXXConversion fname::operator int() at $TESTCASE_ROOT/test.cpp:18:5 *) (Nscoped (Nglobal (Nid "fname")) (Nop_conv function_qualifiers.N Tint)) ::
  
      (* Function operator""_lit(unsigned long long) at $TESTCASE_ROOT/test.cpp:20:1 *) (Nglobal (Nop_lit "_lit" (Tulonglong :: nil))) ::
  
      (* CXXDestructor extra::~extra() at $TESTCASE_ROOT/test.cpp:26:5 *) (Nscoped (Nglobal (Nid "extra")) Ndtor) ::
  
      (* CXXMethod extra::args() at $TESTCASE_ROOT/test.cpp:32:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.N "args" nil)) ::
  
      (* CXXMethod extra::args(int, bool) at $TESTCASE_ROOT/test.cpp:33:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.N "args" (Tint :: Tbool :: nil))) ::
  
      (* CXXMethod extra::l() & at $TESTCASE_ROOT/test.cpp:34:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.Nl "l" nil)) ::
  
      (* CXXMethod extra::r() && at $TESTCASE_ROOT/test.cpp:35:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.Nr "r" nil)) ::
  
      (* CXXMethod extra::c() const at $TESTCASE_ROOT/test.cpp:36:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.Nc "c" nil)) ::
  
      (* CXXMethod extra::v() volatile at $TESTCASE_ROOT/test.cpp:37:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.Nv "v" nil)) ::
  
      (* CXXMethod extra::cvl() const volatile & at $TESTCASE_ROOT/test.cpp:38:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifiers.Ncvl "cvl" nil)) ::
  
      (* CXXRecord fname at $TESTCASE_ROOT/test.cpp:10:1 *) (Nglobal (Nid "fname")) ::
  
      (* CXXRecord extra at $TESTCASE_ROOT/test.cpp:24:1 *) (Nglobal (Nid "extra")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
