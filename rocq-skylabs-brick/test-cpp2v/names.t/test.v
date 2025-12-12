Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.syntax.
Require bluerock.lang.cpp.syntax.supported.


Require test.test_cpp.
Require test.anonymous_cpp.

Eval vm_compute in supported.check.translation_unit test_cpp.module.

Definition is_Some {T} (a : option T) : Prop :=
  match a with
  | None => False
  | Some _ => True
  end.

(* check that the function exists *)
Goal is_Some $ test_cpp.module.(symbols) !!
        (Ninst (Nscoped (Nscoped (Ninst (Nglobal (Nfunction function_qualifiers.N "run" ( Tint :: Tnullptr :: nil)))
              ((Atype Tint) :: (Atype Tnullptr) :: nil)) (Nanon 0)) (Nop function_qualifiers.Nc OOCall (Tlong :: Tint :: Tnullptr :: nil)))
        ((Atype Tlong) :: nil)).
Proof. exact I. Qed.

Definition type_exists (tu : translation_unit) (n : name) : Prop :=
  is_Some (tu.(types) !! n).

Definition field_exists (tu : translation_unit) (f : field) : Prop :=
  match f with
  | Nscoped nm f =>
      let has_field mems :=
        if List.existsb (fun m => bool_decide (m.(mem_name) = f)) mems then True else False in
      match tu.(types) !! nm with
      | Some (Gstruct s) => has_field s.(s_fields)
      | Some (Gunion u) => has_field u.(u_fields)
      | _ => False
      end
  | _ => False
  end.

Ltac solve_exists :=
  try solve [ vm_compute; exact I ];
  match goal with
  | |- ?G =>
      fail "Failed to solve " G
  end.


Succeed Example _0 : type_exists anonymous_cpp.module "C" := ltac:(solve_exists).
Succeed Example _0 : field_exists anonymous_cpp.module "C::_a" := ltac:(solve_exists).
Succeed Example _1 : type_exists anonymous_cpp.module "C::@_a" := ltac:(solve_exists).
Succeed Example _1 : field_exists anonymous_cpp.module "C::@_a::x" := ltac:(solve_exists).

Succeed Example _0 : field_exists anonymous_cpp.module "C::_b" := ltac:(solve_exists).
Succeed Example _2 : type_exists anonymous_cpp.module "C::@_b" := ltac:(solve_exists).
Succeed Example _2 : field_exists anonymous_cpp.module "C::@_b::x" := ltac:(solve_exists).
Succeed Example _2 : field_exists anonymous_cpp.module "C::@_b::y" := ltac:(solve_exists).

Succeed Example _3 : type_exists anonymous_cpp.module "D" := ltac:(solve_exists).
Succeed Example _4 : type_exists anonymous_cpp.module "D::.a" := ltac:(solve_exists).
Succeed Example _4 : field_exists anonymous_cpp.module "D::.a::a" := ltac:(solve_exists).
Succeed Example _4 : field_exists anonymous_cpp.module "D::.a::b" := ltac:(solve_exists).
Succeed Example _5 : type_exists anonymous_cpp.module "D::.a::@a" := ltac:(solve_exists).
Succeed Example _5 : field_exists anonymous_cpp.module "D::.a::@a::x" := ltac:(solve_exists).
Succeed Example _6 : type_exists anonymous_cpp.module "D::.a::@b" := ltac:(solve_exists).
Succeed Example _5 : field_exists anonymous_cpp.module "D::.a::@b::y" := ltac:(solve_exists).
