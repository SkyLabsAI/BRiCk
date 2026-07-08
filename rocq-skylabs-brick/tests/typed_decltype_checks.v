Require Import skylabs.lang.cpp.syntax.typed.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[duplicates(error)]
cpp.prog source flags "-std=c++20" prog cpp:{{
  struct C {
    int f;
    C(int);
  };

  struct D {
    D();
  };

  void not_ctor(C*, int) {}

  int global_int;
}}.

Definition C_name : name := Nglobal (Nid "C").
Definition D_name : name := Nglobal (Nid "D").
Definition C_ctor_int : name := Nscoped C_name (Nctor (Tint :: nil)).
Definition not_ctor_name : name :=
  Nglobal (Nfunction function_qualifiers.N "not_ctor" (Tptr (Tnamed C_name) :: Tint :: nil)).
Definition global_int_name : name := Nglobal (Nid "global_int").
Definition C_field_f : name := Nscoped C_name (Nid "f").
Definition C_field_missing : name := Nscoped C_name (Nid "missing").
Definition missing_global : name := Nglobal (Nid "missing").

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
