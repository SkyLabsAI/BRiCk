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
      (NLocInfo 0%uint63 (Nglobal
          (ANLocInfo 0%uint63 (Nfunction function_qualifiers.N "fid" nil)))) ::
  
      (NLocInfo 1%uint63 (Nscoped
          (NLocInfo 2%uint63 (Nglobal
              (ANLocInfo 2%uint63 (Nid "fname"))))
          (ANLocInfo 1%uint63 (Nctor nil)))) ::
  
      (NLocInfo 3%uint63 (Nscoped
          (NLocInfo 2%uint63 (Nglobal
              (ANLocInfo 2%uint63 (Nid "fname"))))
          (ANLocInfo 3%uint63 Ndtor))) ::
  
      (NLocInfo 4%uint63 (Nscoped
          (NLocInfo 2%uint63 (Nglobal
              (ANLocInfo 2%uint63 (Nid "fname"))))
          (ANLocInfo 4%uint63 (Nop function_qualifiers.N OOPlusPlus nil)))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 2%uint63 (Nglobal
              (ANLocInfo 2%uint63 (Nid "fname"))))
          (ANLocInfo 5%uint63 (Nop_conv function_qualifiers.N Tint)))) ::
  
      (NLocInfo 6%uint63 (Nglobal
          (ANLocInfo 6%uint63 (Nop_lit "_lit" (Tulonglong :: nil))))) ::
  
      (NLocInfo 7%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 7%uint63 Ndtor))) ::
  
      (NLocInfo 9%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 9%uint63 (Nfunction function_qualifiers.N "args" nil)))) ::
  
      (NLocInfo 10%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 10%uint63 (Nfunction function_qualifiers.N "args" (Tint :: Tbool :: nil))))) ::
  
      (NLocInfo 11%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 11%uint63 (Nfunction function_qualifiers.Nl "l" nil)))) ::
  
      (NLocInfo 12%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 12%uint63 (Nfunction function_qualifiers.Nr "r" nil)))) ::
  
      (NLocInfo 13%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 13%uint63 (Nfunction function_qualifiers.Nc "c" nil)))) ::
  
      (NLocInfo 14%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 14%uint63 (Nfunction function_qualifiers.Nv "v" nil)))) ::
  
      (NLocInfo 15%uint63 (Nscoped
          (NLocInfo 8%uint63 (Nglobal
              (ANLocInfo 8%uint63 (Nid "extra"))))
          (ANLocInfo 15%uint63 (Nfunction function_qualifiers.Ncvl "cvl" nil)))) ::
  
      (NLocInfo 2%uint63 (Nglobal
          (ANLocInfo 2%uint63 (Nid "fname")))) ::
  
      (NLocInfo 8%uint63 (Nglobal
          (ANLocInfo 8%uint63 (Nid "extra")))) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
  
  Definition file_names : array PrimString.string :=
    let result := PArray.make 1%uint63 "unknown_file"%pstring in
    let result := PArray.set result 0%uint63 "$TESTCASE_ROOT/test.cpp"%pstring in
    result.
  
  Definition loc_table : array locations :=
    let result := PArray.make 16%uint63 dummy_locations in
    let result := PArray.set result 0%uint63 (Build_locations (Build_location 0%uint63 245%uint63 9%uint63 1%uint63) (Build_location 0%uint63 245%uint63 9%uint63 1%uint63)) in
    let result := PArray.set result 1%uint63 (Build_locations (Build_location 0%uint63 275%uint63 11%uint63 5%uint63) (Build_location 0%uint63 275%uint63 11%uint63 5%uint63)) in
    let result := PArray.set result 2%uint63 (Build_locations (Build_location 0%uint63 257%uint63 10%uint63 1%uint63) (Build_location 0%uint63 257%uint63 10%uint63 1%uint63)) in
    let result := PArray.set result 3%uint63 (Build_locations (Build_location 0%uint63 288%uint63 12%uint63 5%uint63) (Build_location 0%uint63 288%uint63 12%uint63 5%uint63)) in
    let result := PArray.set result 4%uint63 (Build_locations (Build_location 0%uint63 450%uint63 17%uint63 5%uint63) (Build_location 0%uint63 450%uint63 17%uint63 5%uint63)) in
    let result := PArray.set result 5%uint63 (Build_locations (Build_location 0%uint63 475%uint63 18%uint63 5%uint63) (Build_location 0%uint63 475%uint63 18%uint63 5%uint63)) in
    let result := PArray.set result 6%uint63 (Build_locations (Build_location 0%uint63 494%uint63 20%uint63 1%uint63) (Build_location 0%uint63 494%uint63 20%uint63 1%uint63)) in
    let result := PArray.set result 7%uint63 (Build_locations (Build_location 0%uint63 612%uint63 26%uint63 5%uint63) (Build_location 0%uint63 612%uint63 26%uint63 5%uint63)) in
    let result := PArray.set result 8%uint63 (Build_locations (Build_location 0%uint63 572%uint63 24%uint63 1%uint63) (Build_location 0%uint63 572%uint63 24%uint63 1%uint63)) in
    let result := PArray.set result 9%uint63 (Build_locations (Build_location 0%uint63 775%uint63 32%uint63 5%uint63) (Build_location 0%uint63 775%uint63 32%uint63 5%uint63)) in
    let result := PArray.set result 10%uint63 (Build_locations (Build_location 0%uint63 792%uint63 33%uint63 5%uint63) (Build_location 0%uint63 792%uint63 33%uint63 5%uint63)) in
    let result := PArray.set result 11%uint63 (Build_locations (Build_location 0%uint63 824%uint63 34%uint63 5%uint63) (Build_location 0%uint63 824%uint63 34%uint63 5%uint63)) in
    let result := PArray.set result 12%uint63 (Build_locations (Build_location 0%uint63 840%uint63 35%uint63 5%uint63) (Build_location 0%uint63 840%uint63 35%uint63 5%uint63)) in
    let result := PArray.set result 13%uint63 (Build_locations (Build_location 0%uint63 857%uint63 36%uint63 5%uint63) (Build_location 0%uint63 857%uint63 36%uint63 5%uint63)) in
    let result := PArray.set result 14%uint63 (Build_locations (Build_location 0%uint63 877%uint63 37%uint63 5%uint63) (Build_location 0%uint63 877%uint63 37%uint63 5%uint63)) in
    let result := PArray.set result 15%uint63 (Build_locations (Build_location 0%uint63 900%uint63 38%uint63 5%uint63) (Build_location 0%uint63 900%uint63 38%uint63 5%uint63)) in
    result.
