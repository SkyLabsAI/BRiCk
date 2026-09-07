Require Import skylabs.lang.cpp.syntax.typed.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.parser.

Definition C_name : name := Nglobal (Nid "C").
Definition D_name : name := Nglobal (Nid "D").
Definition C_ctor_int : name := Nscoped C_name (Nctor (Tint :: nil)).
Definition not_ctor_name : name :=
  Nglobal (Nfunction function_qualifiers.N "not_ctor" (Tptr (Tnamed C_name) :: Tint :: nil)).
Definition global_int_name : name := Nglobal (Nid "global_int").
Definition C_field_f : name := Nscoped C_name (Nid "f").
Definition C_field_missing : name := Nscoped C_name (Nid "missing").
Definition missing_global : name := Nglobal (Nid "missing").

Definition C_struct : Struct :=
  Build_Struct nil
    (mkMember (Nid "f") Tint false None {| li_offset := 0 |} :: nil)
    nil nil (Nscoped C_name Ndtor) true None POD 4 4.

Definition D_struct : Struct :=
  Build_Struct nil nil nil nil (Nscoped D_name Ndtor) true None POD 1 1.

Definition C_ctor : Ctor :=
  Build_Ctor C_name (("x"%pstring, Tint) :: nil) CC_C Ar_Definite
    exception_spec.Unknown None.

Definition D_ctor : Ctor :=
  Build_Ctor D_name nil CC_C Ar_Definite exception_spec.Unknown None.

Definition not_ctor : Func :=
  Build_Func Tvoid (("self"%pstring, Tptr (Tnamed C_name)) :: ("x"%pstring, Tint) :: nil)
    CC_C Ar_Definite exception_spec.Unknown None.

Definition source : translation_unit :=
  Eval vm_compute in
    fst (parser.translation_unit.list_decls
      (parser.Dstruct C_name (Some C_struct) ::
       parser.Dstruct D_name (Some D_struct) ::
       parser.Dconstructor C_ctor_int C_ctor ::
       parser.Dconstructor (Nscoped D_name (Nctor nil)) D_ctor ::
       parser.Dfunction not_ctor_name not_ctor ::
       parser.Dvariable global_int_name Tint global_init.NoInit ::
       nil)
      abi.abi_default).

Goal exists ov, source.(symbols) !! C_ctor_int = Some ov.
Proof. vm_compute. eauto. Qed.

Goal exists ov, source.(symbols) !! not_ctor_name = Some ov.
Proof. vm_compute. eauto. Qed.

Goal trace.runO (typed.decltype.check_tu source) = Some tt.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor C_ctor_int (Eint 0 Tint :: nil) (Tnamed C_name))) =
     Some (Tnamed C_name).
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor C_ctor_int (Eint 0 Tint :: nil)
          (Tarray (Tnamed C_name) 3))) =
     Some (Tarray (Tnamed C_name) 3).
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Esizeof (inr (Eglobal C_field_f Tint)) Tsize_t)) =
     Some Tsize_t.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source (Eglobal missing_global Tint)) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source (Eglobal global_int_name Tbool)) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source (Eglobal C_field_missing Tint)) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source (Eglobal C_field_f Tbool)) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor (Nscoped C_name (Nctor nil)) nil (Tnamed C_name))) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor not_ctor_name (Eint 0 Tint :: nil) (Tnamed C_name))) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor C_ctor_int nil (Tnamed C_name))) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor C_ctor_int (Enull :: nil) (Tnamed C_name))) = None.
Proof. vm_compute. reflexivity. Qed.

Goal trace.runO (typed.decltype.of_expr source
       (Econstructor C_ctor_int (Eint 0 Tint :: nil) (Tnamed D_name))) = None.
Proof. vm_compute. reflexivity. Qed.
