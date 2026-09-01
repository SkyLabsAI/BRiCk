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
              (ANLocInfo 1%uint63 Nanonymous)))
          (ANLocInfo 0%uint63 (Nid "inhabit_ns")))) ::
  
      (NLocInfo 2%uint63 (Nscoped
          (NLocInfo 3%uint63 (Nglobal
              (ANLocInfo 3%uint63 (Nid "container"))))
          (ANLocInfo 2%uint63 (Nctor nil)))) ::
  
      (NLocInfo 4%uint63 (Nscoped
          (NLocInfo 3%uint63 (Nglobal
              (ANLocInfo 3%uint63 (Nid "container"))))
          (ANLocInfo 4%uint63 Ndtor))) ::
  
      (NLocInfo 3%uint63 (Nglobal
          (ANLocInfo 3%uint63 (Nid "container")))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 3%uint63 (Nglobal
              (ANLocInfo 3%uint63 (Nid "container"))))
          (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s")))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 5%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))
          (ANLocInfo 5%uint63 (Nctor nil)))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 5%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))
          (ANLocInfo 5%uint63 (Nctor ((Tref (Qconst (Tnamed
                      (NLocInfo 5%uint63 (Nscoped
                          (NLocInfo 3%uint63 (Nglobal
                              (ANLocInfo 3%uint63 (Nid "container"))))
                          (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))))) :: nil))))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 5%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))
          (ANLocInfo 5%uint63 (Nop function_qualifiers.N OOEqual ((Tref (Qconst (Tnamed
                      (NLocInfo 5%uint63 (Nscoped
                          (NLocInfo 3%uint63 (Nglobal
                              (ANLocInfo 3%uint63 (Nid "container"))))
                          (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))))) :: nil))))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 5%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))
          (ANLocInfo 5%uint63 (Nctor ((Trv_ref (Tnamed
                    (NLocInfo 5%uint63 (Nscoped
                        (NLocInfo 3%uint63 (Nglobal
                            (ANLocInfo 3%uint63 (Nid "container"))))
                        (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s")))))) :: nil))))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 5%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))
          (ANLocInfo 5%uint63 (Nop function_qualifiers.N OOEqual ((Trv_ref (Tnamed
                    (NLocInfo 5%uint63 (Nscoped
                        (NLocInfo 3%uint63 (Nglobal
                            (ANLocInfo 3%uint63 (Nid "container"))))
                        (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s")))))) :: nil))))) ::
  
      (NLocInfo 5%uint63 (Nscoped
          (NLocInfo 5%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 5%uint63 (Nrecord_by_field "inhabit_s"))))
          (ANLocInfo 5%uint63 Ndtor))) ::
  
      (NLocInfo 6%uint63 (Nscoped
          (NLocInfo 3%uint63 (Nglobal
              (ANLocInfo 3%uint63 (Nid "container"))))
          (ANLocInfo 6%uint63 (Nrecord_by_field "inhabit_u")))) ::
  
      (NLocInfo 6%uint63 (Nscoped
          (NLocInfo 6%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 6%uint63 (Nrecord_by_field "inhabit_u"))))
          (ANLocInfo 6%uint63 (Nctor ((Tref (Qconst (Tnamed
                      (NLocInfo 6%uint63 (Nscoped
                          (NLocInfo 3%uint63 (Nglobal
                              (ANLocInfo 3%uint63 (Nid "container"))))
                          (ANLocInfo 6%uint63 (Nrecord_by_field "inhabit_u"))))))) :: nil))))) ::
  
      (NLocInfo 6%uint63 (Nscoped
          (NLocInfo 6%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 6%uint63 (Nrecord_by_field "inhabit_u"))))
          (ANLocInfo 6%uint63 (Nctor ((Trv_ref (Tnamed
                    (NLocInfo 6%uint63 (Nscoped
                        (NLocInfo 3%uint63 (Nglobal
                            (ANLocInfo 3%uint63 (Nid "container"))))
                        (ANLocInfo 6%uint63 (Nrecord_by_field "inhabit_u")))))) :: nil))))) ::
  
      (NLocInfo 6%uint63 (Nscoped
          (NLocInfo 6%uint63 (Nscoped
              (NLocInfo 3%uint63 (Nglobal
                  (ANLocInfo 3%uint63 (Nid "container"))))
              (ANLocInfo 6%uint63 (Nrecord_by_field "inhabit_u"))))
          (ANLocInfo 6%uint63 Ndtor))) ::
  
      (NLocInfo 7%uint63 (Nglobal
          (ANLocInfo 7%uint63 (Nenum_by_enumerator "inhabit_e")))) ::
  
      (NLocInfo 8%uint63 (Nscoped
          (NLocInfo 7%uint63 (Nglobal
              (ANLocInfo 7%uint63 (Nenum_by_enumerator "inhabit_e"))))
          (ANLocInfo 8%uint63 (Nid "inhabit_e")))) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
  
  Definition file_names : array PrimString.string :=
    let result := PArray.make 1%uint63 "unknown_file"%pstring in
    let result := PArray.set result 0%uint63 "$TESTCASE_ROOT/test.cpp"%pstring in
    result.
  
  Definition loc_table : array locations :=
    let result := PArray.make 9%uint63 dummy_locations in
    let result := PArray.set result 0%uint63 (Build_locations (Build_location 0%uint63 256%uint63 9%uint63 5%uint63) (Build_location 0%uint63 256%uint63 9%uint63 5%uint63)) in
    let result := PArray.set result 1%uint63 (Build_locations (Build_location 0%uint63 241%uint63 8%uint63 1%uint63) (Build_location 0%uint63 241%uint63 8%uint63 1%uint63)) in
    let result := PArray.set result 2%uint63 (Build_locations (Build_location 0%uint63 299%uint63 12%uint63 5%uint63) (Build_location 0%uint63 299%uint63 12%uint63 5%uint63)) in
    let result := PArray.set result 3%uint63 (Build_locations (Build_location 0%uint63 277%uint63 11%uint63 1%uint63) (Build_location 0%uint63 277%uint63 11%uint63 1%uint63)) in
    let result := PArray.set result 4%uint63 (Build_locations (Build_location 0%uint63 316%uint63 13%uint63 5%uint63) (Build_location 0%uint63 316%uint63 13%uint63 5%uint63)) in
    let result := PArray.set result 5%uint63 (Build_locations (Build_location 0%uint63 515%uint63 19%uint63 5%uint63) (Build_location 0%uint63 515%uint63 19%uint63 5%uint63)) in
    let result := PArray.set result 6%uint63 (Build_locations (Build_location 0%uint63 558%uint63 23%uint63 5%uint63) (Build_location 0%uint63 558%uint63 23%uint63 5%uint63)) in
    let result := PArray.set result 7%uint63 (Build_locations (Build_location 0%uint63 604%uint63 27%uint63 1%uint63) (Build_location 0%uint63 604%uint63 27%uint63 1%uint63)) in
    let result := PArray.set result 8%uint63 (Build_locations (Build_location 0%uint63 611%uint63 27%uint63 8%uint63) (Build_location 0%uint63 611%uint63 27%uint63 8%uint63)) in
    result.
