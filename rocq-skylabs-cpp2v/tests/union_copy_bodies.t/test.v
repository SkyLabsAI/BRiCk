From stdpp Require Import fin_maps.
Require Import Stdlib.Strings.String.
#[local] Open Scope string_scope.
Require Import skylabs.lang.cpp.syntax skylabs.lang.cpp.semantics.

Require test.src_cpp.

(** The kind of body of each constructor and method of a union. *)
Definition body_kind {A} (b : option (OrDefault A)) : string :=
  match b with
  | None => "none"
  | Some Defaulted => "Defaulted"
  | Some (CompilerProvided _) => "CompilerProvided"
  | Some (UserDefined _) => "UserDefined"
  end.

Definition union_member_bodies (tu : translation_unit) (cls : globname) :
    list (obj_name * string) :=
  List.flat_map (fun '(n, o) =>
    match o with
    | Omethod m =>
        if bool_decide (m.(m_class) = cls) then [(n, body_kind m.(m_body))] else []
    | Oconstructor c =>
        if bool_decide (c.(c_class) = cls) then [(n, body_kind c.(c_body))] else []
    | _ => []
    end) (map_to_list tu.(symbols)).

(** [U]'s copy/move constructors and assignment operators are [Defaulted]. *)
Eval vm_compute in union_member_bodies src_cpp.source "U".
(** [N]'s have no body. *)
Eval vm_compute in union_member_bodies src_cpp.source "N".

Goal True.
Proof.
  idtac "Success!".
  exact I.
Qed.
