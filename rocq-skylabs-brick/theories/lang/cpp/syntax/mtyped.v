(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.mcore.
Require Import bluerock.lang.cpp.syntax.types.
Require Import bluerock.lang.cpp.syntax.typing.
Require Import bluerock.lang.cpp.syntax.stmt.
Require Import bluerock.lang.cpp.syntax.translation_unit.
Require Import bluerock.lang.cpp.syntax.typed.
Require Import bluerock.lang.cpp.syntax.templates.
Require Import bluerock.lang.cpp.syntax.untemp.

Import UPoly.

Definition tu_to_ext (tu : translation_unit) : typed.decltype.internal.ext_tu :=
  {| typed.decltype.internal.ext_symbols nm :=
      match trace.runO $ untempN nm with
      | Some nm =>
          match type_of_value <$> tu.(symbols) !! nm with
          | Some t => trace.runO $ totempT t
          | None => None
          end
      | None => None
      end
  ; typed.decltype.internal.ext_types nm :=
      match trace.runO $ untempN nm with
      | Some nm =>
          match tu.(types) !! nm return option MGlobDecl with
          | Some t => trace.runO $ totempGD t
          | None => None
          end
      | None => None
      end
  |}.

#[local] Open Scope monad_scope.
Definition check_mtu (mtu : Mtranslation_unit) (tu : translation_unit) : trace.M Error.t unit :=
  let M := readerT.M _ (trace.M Error.t) in
  let fn (nm_v : Mname * template MObjValue) : M unit :=
    decltype.internal.check_obj_value nm_v.2.(template_value)
  in
  let ext_tu := tu_to_ext tu in
  let* _ :=
    readerT.run (traverse (F:=M) (T:=eta list) fn $ TM.elements mtu.(msymbols)) ext_tu
  in
  mret tt.
