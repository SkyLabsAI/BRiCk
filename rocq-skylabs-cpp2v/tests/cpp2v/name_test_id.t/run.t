  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import skylabs.lang.cpp.mparser.
  
  Require Import Stdlib.Array.PArray.
  Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
  Require Import skylabs.lang.cpp.syntax.loc_info.
  #[local] Open Scope array_scope.
  #[local] Open Scope uint63_scope.
  #[local] Open Scope pstring_scope.
  
  Definition module_names : list Mname :=
    (
      (NLocInfo 0%uint63 (Nscoped
          (NLocInfo 1%uint63 (Nglobal
              (ANLocInfo 1%uint63 (Nid "ns"))))
          (ANLocInfo 0%uint63 (Nid "inhabit")))) ::
  
      (NLocInfo 2%uint63 (Nglobal
          (ANLocInfo 2%uint63 (Nid "c")))) ::
  
      (NLocInfo 3%uint63 (Nglobal
          (ANLocInfo 3%uint63 (Nid "s")))) ::
  
      (NLocInfo 4%uint63 (Nglobal
          (ANLocInfo 4%uint63 (Nid "u")))) ::
  
      (NLocInfo 5%uint63 (Nglobal
          (ANLocInfo 5%uint63 (Nid "e1")))) ::
  
      (NLocInfo 6%uint63 (Nglobal
          (ANLocInfo 6%uint63 (Nid "e2")))) ::
  
      (NLocInfo 7%uint63 (Nglobal
          (ANLocInfo 7%uint63 (Nid "t1")))) ::
  
      (NLocInfo 8%uint63 (Nglobal
          (ANLocInfo 8%uint63 (Nid "t2")))) ::
  
      (NLocInfo 9%uint63 (Nglobal
          (ANLocInfo 9%uint63 (Nid "v")))) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
  
  Definition file_names : array PrimString.string :=
    let result := PArray.make 1%uint63 "unknown_file"%pstring in
    let result := PArray.set result 0%uint63 "$TESTCASE_ROOT/test.cpp"%pstring in
    result.
  
  Definition loc_table : array locations :=
    let result := PArray.make 10%uint63 dummy_locations in
    let result := PArray.set result 0%uint63 (Build_locations (Build_location 0%uint63 258%uint63 10%uint63 5%uint63) (Build_location 0%uint63 258%uint63 10%uint63 5%uint63)) in
    let result := PArray.set result 1%uint63 (Build_locations (Build_location 0%uint63 240%uint63 9%uint63 1%uint63) (Build_location 0%uint63 240%uint63 9%uint63 1%uint63)) in
    let result := PArray.set result 2%uint63 (Build_locations (Build_location 0%uint63 276%uint63 12%uint63 1%uint63) (Build_location 0%uint63 276%uint63 12%uint63 1%uint63)) in
    let result := PArray.set result 3%uint63 (Build_locations (Build_location 0%uint63 285%uint63 13%uint63 1%uint63) (Build_location 0%uint63 285%uint63 13%uint63 1%uint63)) in
    let result := PArray.set result 4%uint63 (Build_locations (Build_location 0%uint63 295%uint63 14%uint63 1%uint63) (Build_location 0%uint63 295%uint63 14%uint63 1%uint63)) in
    let result := PArray.set result 5%uint63 (Build_locations (Build_location 0%uint63 304%uint63 15%uint63 1%uint63) (Build_location 0%uint63 304%uint63 15%uint63 1%uint63)) in
    let result := PArray.set result 6%uint63 (Build_locations (Build_location 0%uint63 316%uint63 16%uint63 1%uint63) (Build_location 0%uint63 316%uint63 16%uint63 1%uint63)) in
    let result := PArray.set result 7%uint63 (Build_locations (Build_location 0%uint63 334%uint63 17%uint63 1%uint63) (Build_location 0%uint63 334%uint63 17%uint63 1%uint63)) in
    let result := PArray.set result 8%uint63 (Build_locations (Build_location 0%uint63 350%uint63 18%uint63 1%uint63) (Build_location 0%uint63 350%uint63 18%uint63 1%uint63)) in
    let result := PArray.set result 9%uint63 (Build_locations (Build_location 0%uint63 366%uint63 19%uint63 1%uint63) (Build_location 0%uint63 366%uint63 19%uint63 1%uint63)) in
    result.
