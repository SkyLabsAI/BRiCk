(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.error.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.templates.
Require Import bluerock.lang.cpp.syntax.mtraverse.
Import UPoly.

(** * Converting untemplated code between [lang.temp] and [lang.cpp] *)

Module Import internal.
  Import MTraverse.

  #[local] Notation M := (trace.M Error.t).

  mlock Definition Not_representable : Error.t := inhabitant.

  Section convert.
    Definition handle_type : type_handler M := {|
      handle_Tparam _ := mthrow Not_representable;
      handle_Tresult_param _ := mthrow Not_representable;
      handle_Tresult_global _ _ := mthrow Not_representable;
      handle_Tresult_unop _ _ _ := mthrow Not_representable;
      handle_Tresult_binop _ _ _ _ _ := mthrow Not_representable;
      handle_Tresult_call _ _ _ _ := mthrow Not_representable;
      handle_Tresult_member_call _ _ _ _ _ _ := mthrow Not_representable;
      handle_Tresult_parenlist _ _ _ _ := mthrow Not_representable;
      handle_Tresult_member _ _ _ _ := mthrow Not_representable;
      handle_Tnamed _ n := Tnamed <$> n ();
      handle_Tref _ t := Tref <$> t ();
      handle_Trv_ref _ t := Trv_ref <$> t ();
      handle_Tqualified cv _ t := Tqualified cv <$> t ();
    |}.

    Definition handle_expr : expr_handler M := {|
      handle_Eparam _ := mthrow Not_representable;
      handle_Eunresolved_global _ _ := mthrow Not_representable;
      handle_Eunresolved_unop _ _ _ := mthrow Not_representable;
      handle_Eunresolved_binop _ _ _ _ _ := mthrow Not_representable;
      handle_Eunresolved_call _ _ _ _ := mthrow Not_representable;
      handle_Eunresolved_member_call _ _ _ _ _ _ := mthrow Not_representable;
      handle_Eunresolved_parenlist _ _ _ _ := mthrow Not_representable;
      handle_Eunresolved_member _ _ _ _ := mthrow Not_representable;
      handle_expr_type := id;
      handle_Eunresolved_cast _ _ _ _ := mthrow Not_representable;
      handle_unresolved_init _ mt me :=
        match me with
        | None => (fun t => (t, None)) <$> mt ()
        | Some e => pair <$> mt () <*> (Some <$> e.2 ())
        end
    |}.
  End convert.
End internal.

#[local] Notation USE f := (
  f handle_type
    handle_expr
) (only parsing).
#[local] Notation M2S f := (USE f).
#[local] Notation S2M f := (USE f).

Definition untempN := M2S MTraverse.traverseN.
Definition untempT := M2S MTraverse.traverseT.
Definition untempE := M2S MTraverse.traverseE.
Definition untempTA := M2S MTraverse.traverseTA.
Definition untempTP := temp_param.traverse untempT.
Definition untempGD := MTraverse.traverseGD (M2S MTraverse.mk_core_traversal).

Definition totempN := S2M MTraverse.traverseN.
Definition totempT := S2M MTraverse.traverseT.
Definition totempE := S2M MTraverse.traverseE.
Definition totempTA := S2M MTraverse.traverseTA.
Definition totempTP := temp_param.traverse totempT.
Definition totempGD := MTraverse.traverseGD (S2M MTraverse.mk_core_traversal).
