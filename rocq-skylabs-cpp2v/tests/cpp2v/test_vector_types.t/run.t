  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -E 'Dtypedef.*"(v4di|v4di_u|v16qi_u|cu32|cv1|f3_ext|f4_ext|f4_gnu|v4si|v4si_overaligned)"' test_17_cpp.v
      (Dtypedef (Nglobal (Nid "v4di")) (Tvector Tlonglong 4 32))
      (Dtypedef (Nglobal (Nid "v4di_u")) (Tvector Tlonglong 4 1))
      (Dtypedef (Nglobal (Nid "v16qi_u")) (Tvector Tchar 16 1))
      (Dtypedef (Nglobal (Nid "cu32")) (Qconst (Tvector Tlonglong 4 32)))
      (Dtypedef (Nglobal (Nid "cv1")) (Qconst (Tvector Tlonglong 4 1)))
      (Dtypedef (Nglobal (Nid "f3_ext")) (Tunsupported "Typedef f3_ext"))
      (Dtypedef (Nglobal (Nid "f4_ext")) (Tunsupported "Typedef f4_ext"))
      (Dtypedef (Nglobal (Nid "f4_gnu")) (Tvector Tfloat 4 16))
      (Dtypedef (Nglobal (Nid "v4si")) (Tvector Tint 4 16))
      (Dtypedef (Nglobal (Nid "v4si_overaligned")) (Tunsupported "Typedef v4si_overaligned"))
  $ grep -E 'Sreturn_val.*Ealignof' test_17_cpp.v
                  (Sreturn_val (Ealignof (inl (Qconst (Tvector Tlonglong 4 32))) Tulong)) :: nil))))))
                  (Sreturn_val (Ealignof (inl (Qconst (Tvector Tlonglong 4 1))) Tulong)) :: nil))))))
  $ grep -E 'Definition t1 : type|"same_vec_fn"|"same_vec_fn_decl_only"' test_17_cpp.v
  #[local] Definition t1 : type := (Tptr (Tvector Tlonglong 4 32)).
  #[local] Definition n1 : name := (Nglobal (Nfunction function_qualifiers.N "same_vec_fn_decl_only" (t1 :: nil))).
  #[local] Definition n8 : name := (Nglobal (Nfunction function_qualifiers.N "same_vec_fn" (t1 :: nil))).
  #[local] Definition n9 : name := (Nglobal (Nfunction function_qualifiers.N "same_vec_fn" ((Tptr (Tvector Tlonglong 4 32)) :: nil))).
  #[local] Definition n11 : name := (Nglobal (Nfunction function_qualifiers.N "same_vec_fn_decl_only" ((Tptr (Tvector Tlonglong 4 32)) :: nil))).
  $ grep -E '"overload_vec"' test_17_cpp.v
  #[local] Definition n12 : name := (Nglobal (Nfunction function_qualifiers.N "overload_vec" ((Tvector Tfloat 4 16) :: nil))).
  #[local] Definition n13 : name := (Nglobal (Nfunction function_qualifiers.N "overload_vec" ((Tunsupported "Typedef f4_ext") :: nil))).
