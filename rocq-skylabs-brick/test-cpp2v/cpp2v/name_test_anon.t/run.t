  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bluerock.lang.cpp.mparser.
  
  #[local] Open Scope pstring_scope.
  
  Definition module_names : list Mname :=
    (
      (* CXXRecord (anonymous namespace)::inhabit_ns at $TESTCASE_ROOT/test.cpp:9:5 *) (Nscoped (Nglobal Nanonymous) (Nid "inhabit_ns")) ::
  
      (* CXXConstructor container::container() at $TESTCASE_ROOT/test.cpp:12:5 *) (Nscoped (Nglobal (Nid "container")) (Nctor nil)) ::
  
      (* CXXDestructor container::~container() at $TESTCASE_ROOT/test.cpp:13:5 *) (Nscoped (Nglobal (Nid "container")) Ndtor) ::
  
      (* CXXRecord container at $TESTCASE_ROOT/test.cpp:11:1 *) (Nglobal (Nid "container")) ::
  
      (* CXXRecord container::(anonymous struct at $TESTCASE_ROOT/test.cpp:19:5) at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) ::
  
      (* CXXConstructor container::(anonymous struct)::(anonymous struct at $TESTCASE_ROOT/test.cpp:19:5)() at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) (Nctor nil)) ::
  
      (* CXXConstructor container::(anonymous struct)::(anonymous struct at $TESTCASE_ROOT/test.cpp:19:5)(const (anonymous struct at $TESTCASE_ROOT/test.cpp:19:5) &) at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) (Nctor ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s"))))) :: nil))) ::
  
      (* CXXMethod container::(anonymous struct)::operator=(const (anonymous struct at $TESTCASE_ROOT/test.cpp:19:5) &) at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) (Nop function_qualifiers.N OOEqual ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s"))))) :: nil))) ::
  
      (* CXXConstructor container::(anonymous struct)::(anonymous struct at $TESTCASE_ROOT/test.cpp:19:5)((anonymous struct at $TESTCASE_ROOT/test.cpp:19:5) &&) at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) (Nctor ((Trv_ref (Tnamed (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")))) :: nil))) ::
  
      (* CXXMethod container::(anonymous struct)::operator=((anonymous struct at $TESTCASE_ROOT/test.cpp:19:5) &&) at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) (Nop function_qualifiers.N OOEqual ((Trv_ref (Tnamed (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")))) :: nil))) ::
  
      (* CXXDestructor container::(anonymous struct)::~(anonymous struct at $TESTCASE_ROOT/test.cpp:19:5)() at $TESTCASE_ROOT/test.cpp:19:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_s")) Ndtor) ::
  
      (* CXXRecord container::(anonymous union at $TESTCASE_ROOT/test.cpp:23:5) at $TESTCASE_ROOT/test.cpp:23:5 *) (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_u")) ::
  
      (* CXXConstructor container::(anonymous union)::(anonymous union at $TESTCASE_ROOT/test.cpp:23:5)(const (anonymous union at $TESTCASE_ROOT/test.cpp:23:5) &) at $TESTCASE_ROOT/test.cpp:23:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_u")) (Nctor ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_u"))))) :: nil))) ::
  
      (* CXXConstructor container::(anonymous union)::(anonymous union at $TESTCASE_ROOT/test.cpp:23:5)((anonymous union at $TESTCASE_ROOT/test.cpp:23:5) &&) at $TESTCASE_ROOT/test.cpp:23:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_u")) (Nctor ((Trv_ref (Tnamed (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_u")))) :: nil))) ::
  
      (* CXXDestructor container::(anonymous union)::~(anonymous union at $TESTCASE_ROOT/test.cpp:23:5)() at $TESTCASE_ROOT/test.cpp:23:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nrecord_by_field "inhabit_u")) Ndtor) ::
  
      (* Enum (unnamed enum at $TESTCASE_ROOT/test.cpp:27:1) at $TESTCASE_ROOT/test.cpp:27:1 *) (Nglobal (Nenum_by_enumerator "inhabit_e")) ::
  
      (* EnumConstant inhabit_e at $TESTCASE_ROOT/test.cpp:27:8 *) (Nscoped (Nglobal (Nenum_by_enumerator "inhabit_e")) (Nid "inhabit_e")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
