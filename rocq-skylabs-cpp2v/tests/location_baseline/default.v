Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.parser.
Require skylabs.lang.cpp.mparser.

#[local] Open Scope pstring_scope.
#[local] Definition n1 : name := (Nglobal (Nid "Record")).
#[local] Definition n2 : name := (Nscoped n1 (Nfunction function_qualifiers.Nc "method" (Tint :: nil))).
#[local] Definition n3 : name := (Nscoped n1 (Nctor nil)).
#[local] Definition t1 : type := (Tnamed n1).
#[local] Definition t2 : type := (Tref (Qconst t1)).
#[local] Definition n4 : name := (Nscoped n1 (Nctor (t2 :: nil))).
#[local] Definition t3 : type := (Tref t1).
#[local] Definition n5 : name := (Nscoped n1 (Nop function_qualifiers.N OOEqual (t2 :: nil))).
#[local] Definition t4 : type := (Tnamed n1).
#[local] Definition t5 : type := (Tptr t4).
#[local] Definition t6 : type := (Trv_ref t1).
#[local] Definition n6 : name := (Nscoped n1 (Nctor (t6 :: nil))).
#[local] Definition n7 : name := (Nscoped n1 (Nop function_qualifiers.N OOEqual (t6 :: nil))).
#[local] Definition n8 : name := (Nscoped n1 Ndtor).
#[local] Definition n9 : name := (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" (Tint :: nil))) ((Atype Tint) :: nil)).
#[local] Definition n10 : name := (Nglobal (Nfunction function_qualifiers.N "redeclared" (Tint :: nil))).
#[local] Definition t7 : type := 
(Tfunction type CC_C Ar_Definite Tint (Tint :: nil)).
#[local] Definition t8 : type := (Tptr t7).

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
    (Dstruct n1
      (Some
        (Build_Struct nil
          ((mkMember (field_name.Id "field") Tint false None
              (Build_LayoutInfo 0)) :: nil) (nil) (nil) (Nscoped n1 Ndtor) true None
          POD 4 4)))
    (Dmethod n2 false
      (Build_Method Tint n1 QC (("x", Tint) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some
          (UserDefined
            (Sseq (
                (Sif None None
                  (Ebinop Bgt
                    (Ecast Cl2r (Evar "x" Tint)) (Eint 0%Z Tint) Tbool)
                  (Sreturn_val
                    (Ebinop Badd
                      (Ecast Cl2r
                        (Emember true (Ethis (Tptr (Qconst t4))) (Field (field_name.Id "field") false Tint)))
                      (Ecast Cl2r (Evar "x" Tint)) Tint)) Sskip) ::
                (Sreturn_val
                  (Ecast Cl2r
                    (Emember true (Ethis (Tptr (Qconst t4))) (Field (field_name.Id "field") false Tint)))) :: nil))))))
    (Dconstructor n3
      (Build_Ctor n1 nil CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided (nil,
            (Sseq (nil)))))))
    (Dconstructor n4
      (Build_Ctor n1 (((localname.anon 0), t2) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided ((
              (Build_Initializer (InitField (field_name.Id "field"))
                (Ecast Cl2r
                  (Emember false (Evar (localname.anon 0) t2) (Field (field_name.Id "field") false Tint)))) :: nil),
            (Sseq (nil)))))))
    (Dmethod n5 false
      (Build_Method t3 n1 QM (((localname.anon 0), t2) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided
            (Sseq (
                (Sexpr
                  (Eassign
                    (Emember true (Ethis t5) (Field (field_name.Id "field") false Tint))
                    (Ecast Cl2r
                      (Emember false (Evar (localname.anon 0) t2) (Field (field_name.Id "field") false Tint))) Tint)) ::
                (Sreturn_val
                  (Ederef (Ethis t5) t4)) :: nil))))))
    (Dconstructor n6
      (Build_Ctor n1 (((localname.anon 0), t6) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided ((
              (Build_Initializer (InitField (field_name.Id "field"))
                (Ecast Cl2r
                  (Emember false
                    (Estatic_cast (Cnoop (Trv_ref t1)) t6 (Evar (localname.anon 0) t6)) (Field (field_name.Id "field") false Tint)))) :: nil),
            (Sseq (nil)))))))
    (Dmethod n7 false
      (Build_Method t3 n1 QM (((localname.anon 0), t6) :: nil) CC_C Ar_Definite exception_spec.NoThrow
        (Some
          (CompilerProvided
            (Sseq (
                (Sexpr
                  (Eassign
                    (Emember true (Ethis t5) (Field (field_name.Id "field") false Tint))
                    (Ecast Cl2r
                      (Emember false
                        (Estatic_cast (Cnoop (Trv_ref t1)) t6 (Evar (localname.anon 0) t6)) (Field (field_name.Id "field") false Tint))) Tint)) ::
                (Sreturn_val
                  (Ederef (Ethis t5) t4)) :: nil))))))
    (Ddestructor n8
      (Build_Dtor n1 CC_C exception_spec.NoThrow
        (Some
          (CompilerProvided
            (Sseq (nil))))))
    (Dfunction n9
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ebinop Badd
                    (Ecast Cl2r (Evar "x" Tint))
                    (Ecast Cl2r (Evar "x" Tint)) Tint)) :: nil))))))
    (Dfunction n10
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some (Impl
            (Sseq (
                (Sdecl (
                    (Dvar "value" t1
                      (Some
                        (Einitlist (
                            (Ecast Cl2r (Evar "x" Tint)) :: nil) None t1))) :: nil)) ::
                (Sreturn_val
                  (Emember_call false
                    (inl (n2, Direct,
                        (Tfunction type CC_C Ar_Definite Tint (Tint :: nil))))
                    (Ecast (Cnoop (Tref (Qconst t4))) (Evar "value" t1)) (
                      (Ecall
                        (Ecast Cfun2ptr (Eglobal n9 t7))
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
    (Dinstantiation n9
      (Ninst (Nglobal (Nfunction function_qualifiers.N "twice" ((Tparam "T") :: nil))) ((Atype (Tparam "T")) :: nil)) ((Atype Tint) :: nil)) :: nil).
Definition source := skylabs.lang.cpp.mparser.tu.with_templates static__source meta__source.
#[deprecated(note="use [source] instead.")]
Abbreviation module := source (only parsing).
