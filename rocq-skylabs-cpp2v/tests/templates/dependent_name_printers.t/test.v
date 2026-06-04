Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.mparser.
Require Import test_17_cpp_templates.

Definition lookup_function (n : name) : option Func :=
  match templates.(msymbols) !! n with
  | Some template =>
    match template.(template_value) with
    | Ofunction f => Some f
    | _ => None
    end
  | None => None
  end.

Definition lookup_body (n : Mname) : option MStmt :=
  match lookup_function n with
  | Some f =>
    match f.(f_body) with
    | Some (Impl s) => Some s
    | _ => None
    end
  | None => None
  end.

Definition template_function_name
    (name : ident) (params : list Mtype) (args : list Mtemp_arg) : Mname :=
  Ninst (Nglobal (Nfunction function_qualifiers.N name params)) args.

Definition known : Mtype := Tnamed (Nglobal (Nid "Known")).
Definition known_ptr : Mtype := Tptr known.

Definition paren_member_call_name : Mname :=
  template_function_name "paren_member_call" [known_ptr] [Atype (Tparam "T")].

Definition cast_member_call_name : Mname :=
  template_function_name "cast_member_call" [known_ptr] [Atype (Tparam "T")].

Definition pseudo_destructor_name : Mname :=
  template_function_name "pseudo_destructor" [Tptr (Tparam "T")] [Atype (Tparam "T")].

Definition unresolved_member_name : Mname :=
  template_function_name "unresolved_member" [Tparam "T"] [Atype (Tparam "T")].

Definition unresolved_conversion_name : Mname :=
  template_function_name "unresolved_conversion" [Tparam "T"] [Atype (Tparam "T")].

Definition paren_call_name : Mname :=
  template_function_name "paren_call" [Tparam "F"] [Atype (Tparam "F")].

Definition scope_value_name : Mname :=
  template_function_name "scope_value" [] [Atype (Tparam "T")].

Definition scope_call_name : Mname :=
  template_function_name "scope_call" [] [Atype (Tparam "T")].

Definition scope_template_call_name : Mname :=
  template_function_name "scope_template_call" [] [Atype (Tparam "T")].

Definition member_value_name : Mname :=
  template_function_name "member_value" [Tparam "T"] [Atype (Tparam "T")].

Definition arrow_member_value_name : Mname :=
  template_function_name "arrow_member_value" [Tptr (Tparam "T")] [Atype (Tparam "T")].

Definition member_template_call_name : Mname :=
  template_function_name "member_template_call" [Tparam "T"] [Atype (Tparam "T")].

Definition adl_call_name : Mname :=
  template_function_name "adl_call" [Tparam "T"] [Atype (Tparam "T")].

Definition unary_plus_name : Mname :=
  template_function_name "unary_plus" [Tparam "T"] [Atype (Tparam "T")].

Definition binary_plus_name : Mname :=
  template_function_name "binary_plus" [Tparam "T"; Tparam "T"] [Atype (Tparam "T")].

Definition subscript_name : Mname :=
  template_function_name "subscript" [Tparam "T"] [Atype (Tparam "T")].

Definition pointer_to_member_name : Mname :=
  template_function_name "pointer_to_member"
    [Tparam "T"; Tmember_pointer (Tparam "T") Tint] [Atype (Tparam "T")].

Example paren_member_call_body :
  lookup_body paren_member_call_name =
  Some (Sseq [
    Sreturn_val
      (Emember_call true
        (inl ((Nscoped (Nglobal (Nid "Known"))
                  (Nfunction function_qualifiers.N "member" [])),
              Direct,
              Tfunction Mtype CC_C Ar_Definite Tint []))
        (Ecast Cl2r (Evar "p" known_ptr)) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example cast_member_call_body :
  lookup_body cast_member_call_name =
  Some (Sseq [
    Sreturn_val
      (Emember_call true
        (inl ((Nscoped (Nglobal (Nid "Known"))
                  (Nop_conv function_qualifiers.N Tint)),
              Direct,
              Tfunction Mtype CC_C Ar_Definite Tint []))
        (Ecast Cl2r (Evar "p" known_ptr)) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example pseudo_destructor_body :
  lookup_body pseudo_destructor_name =
  Some (Sseq [
    Sexpr
      (Epseudo_destructor true (Tparam "T")
        (Ecast Cl2r (Evar "p" (Tptr (Tparam "T")))))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example unresolved_member_body :
  lookup_body unresolved_member_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_call
        (Ndependent
          (Tresult_member (Tparam "T") (Nlocal (Nid "member")))) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example unresolved_conversion_body :
  lookup_body unresolved_conversion_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_call
        (Ndependent
          (Tresult_member (Tparam "T")
            (Nlocal (Nop_conv function_qualifiers.N Tint)))) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example paren_call_body :
  lookup_body paren_call_name =
  Some (Sseq [
    Sreturn_val (Eunresolved_call (Nlocal (Nid "f")) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example scope_value_body :
  lookup_body scope_value_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_global (Nscoped (Ndependent (Tparam "T")) (Nid "value")))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example scope_call_body :
  lookup_body scope_call_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_call
        (Nscoped (Ndependent (Tparam "T")) (Nid "func")) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example scope_template_call_body :
  lookup_body scope_template_call_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_call
        (Ninst (Nscoped (Ndependent (Tparam "T")) (Nid "func"))
          [Atype Tint]) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example member_value_body :
  lookup_body member_value_name =
  Some (Sseq [
    Sreturn_val
      (core.Eunresolved_member
        (Evar "p" (Tparam "T")) (Nlocal (Nid "value")))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example arrow_member_value_body :
  lookup_body arrow_member_value_name =
  Some (Sseq [
    Sreturn_val
      (core.Eunresolved_member
        (Eunresolved_unop Rarrow
          (Ecast Cl2r (Evar "p" (Tptr (Tparam "T")))))
        (Nlocal (Nid "value")))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example member_template_call_body :
  lookup_body member_template_call_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_call
        (Ndependent
          (Tresult_member (Tparam "T")
            (Ninst (Nlocal (Nid "func")) [Atype Tint]))) [])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example adl_call_body :
  lookup_body adl_call_name =
  Some (Sseq [
    Sreturn_val
      (Eunresolved_call
        (Nlocal (Nid "adl_target")) [Evar "p" (Tparam "T")])
  ]).
Proof. vm_compute. reflexivity. Qed.

Example unary_plus_body :
  lookup_body unary_plus_name =
  Some (Sseq [
    Sreturn_val (Eunop Uplus (Evar "p" (Tparam "T")) None)
  ]).
Proof. vm_compute. reflexivity. Qed.

Example binary_plus_body :
  lookup_body binary_plus_name =
  Some (Sseq [
    Sreturn_val
      (Ebinop Badd
        (Evar "a" (Tparam "T"))
        (Evar "b" (Tparam "T")) None)
  ]).
Proof. vm_compute. reflexivity. Qed.

Example subscript_body :
  lookup_body subscript_name =
  Some (Sseq [
    Sreturn_val
      (Esubscript (Evar "p" (Tparam "T")) (Eint 0%Z Tint) None)
  ]).
Proof. vm_compute. reflexivity. Qed.

Example pointer_to_member_body :
  lookup_body pointer_to_member_name =
  Some (Sseq [
    Sreturn_val
      (Ebinop Bdotp
        (Evar "obj" (Tparam "T"))
        (Evar "member" (Tmember_pointer (Tparam "T") Tint)) None)
  ]).
Proof. vm_compute. reflexivity. Qed.
