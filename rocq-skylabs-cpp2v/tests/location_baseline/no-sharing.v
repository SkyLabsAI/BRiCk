Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.parser.
Require skylabs.lang.cpp.mparser.

#[local] Open Scope pstring_scope.
cpp.prog static__source
  abi (abi.mkT int_rank.Ilong Signed Signed Little lang_version.Cpp17)
  defns
    (Dtypedef (Nglobal (Nid "__int128_t")) Tint128_t)
    (Dtypedef (Nglobal (Nid "__uint128_t")) Tuint128_t)
    (Dtypedef (Nglobal (Nid "__NSConstantString")) (Tnamed (Nglobal (Nid "__NSConstantString_tag"))))
    (Dtypedef (Nglobal (Nid "__builtin_ms_va_list")) (Tptr Tchar))
    (Dtypedef (Nglobal (Nid "__builtin_va_list")) (Tarray (Tnamed (Nglobal (Nid "__va_list_tag"))) 1))
    (Denum (Nglobal (Nid "Kind")) Tuint ("KZero" :: "KOne" :: nil))
    (Denum_constant (Nscoped (Nglobal (Nid "Kind")) (Nid "KZero")) (Nglobal (Nid "Kind")) Tuint (inr 0%Z)
      (Some
        (Ecast (Cintegral Tuint) (Eint 0%Z Tint))))
    (Denum_constant (Nscoped (Nglobal (Nid "Kind")) (Nid "KOne")) (Nglobal (Nid "Kind")) Tuint (inr 1%Z) None)
    (Dstruct (Nglobal (Nid "Record"))
      (Some
        (Build_Struct nil
          ((mkMember (field_name.Id "field") Tint false None
              (Build_LayoutInfo 0)) :: nil) (nil) (nil) (Nscoped (Nglobal (Nid "Record")) Ndtor) true None
          POD 4 4)))
    (Dmethod (Nscoped (Nglobal (Nid "Record")) (Nfunction function_qualifiers.Nc "method" (Tint :: nil))) false
      (Build_Method Tint (Nglobal (Nid "Record")) QC (("x", Tint) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some
          (UserDefined
            (Sseq (
                (Sif None None
                  (Ebinop Bgt
                    (Ecast Cl2r (Evar "x" Tint)) (Eint 0%Z Tint) Tbool)
                  (Sreturn_val
                    (Ebinop Badd
                      (Ecast Cl2r
                        (Emember true (Ethis (Tptr (Qconst (Tnamed (Nglobal (Nid "Record")))))) (Field (field_name.Id "field") false Tint)))
                      (Ecast Cl2r (Evar "x" Tint)) Tint)) Sskip) ::
                (Sreturn_val
                  (Ecast Cl2r
                    (Emember true (Ethis (Tptr (Qconst (Tnamed (Nglobal (Nid "Record")))))) (Field (field_name.Id "field") false Tint)))) :: nil))))))
    (Dconstructor (Nscoped (Nglobal (Nid "Record")) (Nctor nil))
      (Build_Ctor (Nglobal (Nid "Record")) nil CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided (nil,
            (Sseq (nil)))))))
    (Dconstructor (Nscoped (Nglobal (Nid "Record")) (Nctor ((Tref (Qconst (Tnamed (Nglobal (Nid "Record"))))) :: nil)))
      (Build_Ctor (Nglobal (Nid "Record")) (((localname.anon 0), (Tref (Qconst (Tnamed (Nglobal (Nid "Record")))))) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided ((
              (Build_Initializer (InitField (field_name.Id "field"))
                (Ecast Cl2r
                  (Emember false (Evar (localname.anon 0) (Tref (Qconst (Tnamed (Nglobal (Nid "Record")))))) (Field (field_name.Id "field") false Tint)))) :: nil),
            (Sseq (nil)))))))
    (Dmethod (Nscoped (Nglobal (Nid "Record")) (Nop function_qualifiers.N OOEqual ((Tref (Qconst (Tnamed (Nglobal (Nid "Record"))))) :: nil))) false
      (Build_Method (Tref (Tnamed (Nglobal (Nid "Record")))) (Nglobal (Nid "Record")) QM (((localname.anon 0), (Tref (Qconst (Tnamed (Nglobal (Nid "Record")))))) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided
            (Sseq (
                (Sexpr
                  (Eassign
                    (Emember true (Ethis (Tptr (Tnamed (Nglobal (Nid "Record"))))) (Field (field_name.Id "field") false Tint))
                    (Ecast Cl2r
                      (Emember false (Evar (localname.anon 0) (Tref (Qconst (Tnamed (Nglobal (Nid "Record")))))) (Field (field_name.Id "field") false Tint))) Tint)) ::
                (Sreturn_val
                  (Ederef (Ethis (Tptr (Tnamed (Nglobal (Nid "Record"))))) (Tnamed (Nglobal (Nid "Record"))))) :: nil))))))
    (Dconstructor (Nscoped (Nglobal (Nid "Record")) (Nctor ((Trv_ref (Tnamed (Nglobal (Nid "Record")))) :: nil)))
      (Build_Ctor (Nglobal (Nid "Record")) (((localname.anon 0), (Trv_ref (Tnamed (Nglobal (Nid "Record"))))) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided ((
              (Build_Initializer (InitField (field_name.Id "field"))
                (Ecast Cl2r
                  (Emember false
                    (Estatic_cast (Cnoop (Trv_ref (Tnamed (Nglobal (Nid "Record"))))) (Trv_ref (Tnamed (Nglobal (Nid "Record")))) (Evar (localname.anon 0) (Trv_ref (Tnamed (Nglobal (Nid "Record")))))) (Field (field_name.Id "field") false Tint)))) :: nil),
            (Sseq (nil)))))))
    (Dmethod (Nscoped (Nglobal (Nid "Record")) (Nop function_qualifiers.N OOEqual ((Trv_ref (Tnamed (Nglobal (Nid "Record")))) :: nil))) false
      (Build_Method (Tref (Tnamed (Nglobal (Nid "Record")))) (Nglobal (Nid "Record")) QM (((localname.anon 0), (Trv_ref (Tnamed (Nglobal (Nid "Record"))))) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided
            (Sseq (
                (Sexpr
                  (Eassign
                    (Emember true (Ethis (Tptr (Tnamed (Nglobal (Nid "Record"))))) (Field (field_name.Id "field") false Tint))
                    (Ecast Cl2r
                      (Emember false
                        (Estatic_cast (Cnoop (Trv_ref (Tnamed (Nglobal (Nid "Record"))))) (Trv_ref (Tnamed (Nglobal (Nid "Record")))) (Evar (localname.anon 0) (Trv_ref (Tnamed (Nglobal (Nid "Record")))))) (Field (field_name.Id "field") false Tint))) Tint)) ::
                (Sreturn_val
                  (Ederef (Ethis (Tptr (Tnamed (Nglobal (Nid "Record"))))) (Tnamed (Nglobal (Nid "Record"))))) :: nil))))))
    (Ddestructor (Nscoped (Nglobal (Nid "Record")) Ndtor)
      (Build_Dtor (Nglobal (Nid "Record")) CC_C exception_spec.NoThrow
        (Some
          (CompilerProvided
            (Sseq (nil))))))
    (Dfunction (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" (Tint :: nil))) ((Atype Tint) :: nil))
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ebinop Badd
                    (Ecast Cl2r (Evar "x" Tint))
                    (Ecast Cl2r (Evar "x" Tint)) Tint)) :: nil))))))
    (Dfunction (Nglobal (Nfunction function_qualifiers.N "redeclared" (Tint :: nil)))
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some (Impl
            (Sseq (
                (Sdecl (
                    (Dvar "value" (Tnamed (Nglobal (Nid "Record")))
                      (Some
                        (Einitlist (
                            (Ecast Cl2r (Evar "x" Tint)) :: nil) None (Tnamed (Nglobal (Nid "Record")))))) :: nil)) ::
                (Sreturn_val
                  (Emember_call false
                    (inl ((Nscoped (Nglobal (Nid "Record")) (Nfunction function_qualifiers.Nc "method" (Tint :: nil))), Direct,
                        (Tfunction type CC_C Ar_Definite Tint (Tint :: nil))))
                    (Ecast (Cnoop (Tref (Qconst (Tnamed (Nglobal (Nid "Record")))))) (Evar "value" (Tnamed (Nglobal (Nid "Record"))))) (
                      (Ecall
                        (Ecast Cfun2ptr (Eglobal (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" (Tint :: nil))) ((Atype Tint) :: nil))
                            (Tfunction type CC_C Ar_Definite Tint (Tint :: nil))))
                        (
                          (Ecast Cl2r (Evar "x" Tint)) :: nil)) :: nil))) :: nil)))))).
Import skylabs.lang.cpp.mparser.
#[local] Open Scope pstring_scope.

Definition meta__source : Mtranslation_unit :=
  Eval reduce_translation_unit in Mtranslation_unit.decls (
    (Dtemplated_struct (((Ptype "T"), None) :: nil)
      (Ninst (Nglobal (Nid "Box")) ((Atype (Tparam "T")) :: nil))
      (Some
        (Build_Struct nil
          ((mkMember (field_name.Id "value") (Tparam "T") false None
              (Build_LayoutInfo 0)) :: nil) (nil) (nil) (Nscoped
            (Ninst (Nglobal (Nid "Box")) ((Atype (Tparam "T")) :: nil)) Ndtor) true None
          Standard 0 0))) ::
    (Dtemplated_method (((Ptype "T"), None) :: nil) (Nscoped
        (Ninst (Nglobal (Nid "Box")) ((Atype (Tparam "T")) :: nil)) (Nfunction function_qualifiers.Nc "get" nil)) false
      (Build_Method (Tparam "T") (Ndependent' (Tnamed
            (Ninst (Nglobal (Nid "Box")) ((Atype (Tparam "T")) :: nil)))) QC nil CC_C Ar_Definite exception_spec.MayThrow
        (Some
          (UserDefined
            (Sseq (
                (Sreturn_val
                  (Emember true (Ethis (Tptr (Qconst (Tnamed
                            (Ninst (Nglobal (Nid "Box")) ((Atype (Tparam "T")) :: nil)))))) (Field (field_name.Id "value") false (Tparam "T")))) :: nil)))))) ::
    (Dtemplated_function (((Ptype "T"), None) :: nil)
      (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" ((Tparam "T") :: nil))) ((Atype (Tparam "T")) :: nil))
      (Build_Func (Tparam "T")
        (("x", (Tparam "T")) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ebinop Badd (Evar "x" (Tparam "T")) (Evar "x" (Tparam "T")) None)) :: nil)))))) ::
    (Dinstantiation (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" (Tint :: nil))) ((Atype Tint) :: nil))
      (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" ((Tparam "T") :: nil))) ((Atype (Tparam "T")) :: nil)) ((Atype Tint) :: nil)) :: nil).
Definition source := skylabs.lang.cpp.mparser.tu.with_templates static__source meta__source.
#[deprecated(note="use [source] instead.")]
Abbreviation module := source (only parsing).
