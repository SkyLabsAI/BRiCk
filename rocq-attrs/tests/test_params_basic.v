(************************************************************************)
(* Basic contract: importing attrs.ParamsAttr is enough, and user names  *)
(* called Params do not affect the registered Stdlib/Corelib class.      *)
(************************************************************************)

Require Import attrs.ParamsAttr.

#[params="0"] Definition only_import (x : nat) : nat := x.
Definition only_import_ok : Params only_import 0 := ltac:(typeclasses eauto).

Inductive Params : Type := dummy.
#[params="0"] Definition shadowed (x : nat) : nat := x.
Definition shadowed_ok : Corelib.Classes.Morphisms.Params shadowed 0 :=
  ltac:(typeclasses eauto).

Module LocalShadow.
  Definition Params := nat.
  #[params="0"] Definition shadowed2 (x : nat) : nat := x.
  Definition shadowed2_ok : Corelib.Classes.Morphisms.Params shadowed2 0 :=
    ltac:(typeclasses eauto).
End LocalShadow.

Module AbbrevShadow.
  Abbreviation Params := nat.
  #[params="0"] Definition shadowed3 (x : nat) : nat := x.
  Definition shadowed3_ok : Corelib.Classes.Morphisms.Params shadowed3 0 :=
    ltac:(typeclasses eauto).
End AbbrevShadow.
