  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bluerock.lang.cpp.mparser.
  
  #[local] Open Scope pstring_scope.
  
  Definition module_names : list Mname :=
    (
      (* CXXRecord ns::inhabit at $TESTCASE_ROOT/test.cpp:10:5 *) (Nscoped (Nglobal (Nid "ns")) (Nid "inhabit")) ::
  
      (* CXXRecord c at $TESTCASE_ROOT/test.cpp:12:1 *) (Nglobal (Nid "c")) ::
  
      (* CXXRecord s at $TESTCASE_ROOT/test.cpp:13:1 *) (Nglobal (Nid "s")) ::
  
      (* CXXRecord u at $TESTCASE_ROOT/test.cpp:14:1 *) (Nglobal (Nid "u")) ::
  
      (* Enum e1 at $TESTCASE_ROOT/test.cpp:15:1 *) (Nglobal (Nid "e1")) ::
  
      (* Enum e2 at $TESTCASE_ROOT/test.cpp:16:1 *) (Nglobal (Nid "e2")) ::
  
      (* Typedef t1 at $TESTCASE_ROOT/test.cpp:17:1 *) (Nglobal (Nid "t1")) ::
  
      (* TypeAlias t2 at $TESTCASE_ROOT/test.cpp:18:1 *) (Nglobal (Nid "t2")) ::
  
      (* Var v at $TESTCASE_ROOT/test.cpp:19:1 *) (Nglobal (Nid "v")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
