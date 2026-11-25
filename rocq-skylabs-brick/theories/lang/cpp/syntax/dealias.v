(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.error.
Require Import skylabs.prelude.lens.
Require Import skylabs.upoly.upoly.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.mtraverse.

#[local] Notation translation_unit := translation_unit.translation_unit.

(** * Resolving aliases *)
(**
Expand type aliases using the alias information stored within a
[translation_unit].

NOTE: The current implementation relies on the fact that aliases
are already removed from definitions, e.g.
<<
using T = int;
using U = T;
>>
will be represented the same way as
<<
using T = int;
using U = int;
>>
This avoids the potential for loops and makes de-aliasing structurally
recursive. Without this, we would need to rely on fuel (or well-foundedness
arguments) to fully de-alias a type/name.
*)

#[local] Open Scope monad_scope.
#[local] Notation M := (trace.M Error.t).

Module internal.
  Import UPoly.

  Section resolve.
    Context (tu : translation_unit).

    Definition handle_Tnamed (_ : name) (traverse : unit -> M name) : M type :=
      (fun nm => match translation_unit.resolve_type tu nm with
              | None => Tnamed nm (* this is the best approximation we can make, alternatively, we can fail *)
              | Some t => t
              end) <$> traverse ().
    Definition handle_Tref (_ : type) (traverse : unit -> M type) : M type :=
      tref QM <$> traverse ().
    Definition handle_Trv_ref (_ : type) (traverse : unit -> M type) : M type :=
      trv_ref QM <$> traverse ().

    Definition handle_type : type_handler M :=
      (handle_type_traverse
       &: _handle_Tnamed  .= handle_Tnamed
       &: _handle_Tref    .= handle_Tref
       &: _handle_Trv_ref .= handle_Trv_ref)%lens.
  End resolve.
End internal.

Section resolve.
  Import MTraverse.
  Context (tu : translation_unit).

  #[local] Notation USE f := (
    f (internal.handle_type tu) handle_expr_traverse
  ) (only parsing).

  Definition resolveT := USE traverseT.
  Definition resolveE := USE traverseE.
  Definition resolveTA := USE traverseTA.
  Definition resolveS := USE traverseS.
  Definition resolveVD := USE traverseD.

  #[local] Fixpoint canon_vec_align_T (t : type) : type :=
    match t with
    | Tptr t => Tptr (canon_vec_align_T t)
    | Tref t => Tref (canon_vec_align_T t)
    | Trv_ref t => Trv_ref (canon_vec_align_T t)
    | Tarray t n => Tarray (canon_vec_align_T t) n
    | Tincomplete_array t => Tincomplete_array (canon_vec_align_T t)
    | Tvariable_array t e => Tvariable_array (canon_vec_align_T t) e
    | Tfunction ft =>
        Tfunction $ FunctionType (ft_cc:=ft.(ft_cc)) (ft_arity:=ft.(ft_arity))
          (canon_vec_align_T ft.(ft_return))
          (List.map canon_vec_align_T ft.(ft_params))
    | Tmember_pointer gn t => Tmember_pointer gn (canon_vec_align_T t)
    | Tqualified q t => Tqualified q (canon_vec_align_T t)
    | Tvector elem n al =>
        let elem := canon_vec_align_T elem in
        match translation_unit.vector_elem_size elem with
        | Some esz => Tvector elem n (n * esz)%N
        | None => Tvector elem n al
        end
    | Tnamed n => Tnamed (canon_vec_align_N n)
    | Tenum n => Tenum (canon_vec_align_N n)
    | _ => t
    end
  with canon_vec_align_TA (a : temp_arg) : temp_arg :=
    match a with
    | Atype t => Atype (canon_vec_align_T t)
    | Apack xs => Apack (List.map canon_vec_align_TA xs)
    | Atemplate n => Atemplate (canon_vec_align_N n)
    | _ => a
    end
  with canon_vec_align_AN (a : atomic_name) : atomic_name :=
    match a with
    | Nfunction q f ts => Nfunction q f (List.map canon_vec_align_T ts)
    | Nctor ts => Nctor (List.map canon_vec_align_T ts)
    | Nop q o ts => Nop q o (List.map canon_vec_align_T ts)
    | Nop_conv q t => Nop_conv q (canon_vec_align_T t)
    | Nop_lit i ts => Nop_lit i (List.map canon_vec_align_T ts)
    | _ => a
    end
  with canon_vec_align_N (n : name) : name :=
    match n with
    | Nglobal a => Nglobal (canon_vec_align_AN a)
    | Nscoped n a => Nscoped (canon_vec_align_N n) (canon_vec_align_AN a)
    | Ndependent t => Ndependent (canon_vec_align_T t)
    | Ninst n xs => Ninst (canon_vec_align_N n) (List.map canon_vec_align_TA xs)
    | Nunsupported msg => Nunsupported msg
    end.

  #[local] Definition resolveN (n : name) : M name :=
    trace.map canon_vec_align_N (USE traverseN n).


  (** Resolve a type name in a translation unit. *)
  Definition resolveTN (n : name) : M type :=
    resolveT $ Tnamed n.

  (** Resolve the name of a **value** in a translation unit.
      This uses the information in the alias table to attempt to resolve the symbol.
      If the symbol is not found, then the dealiased symbol is returned but namespace
      aliases are not resolved, because there is no way to know where the (unfound)
      definition is supposed to live.
   *)
  Definition resolveValue (n : name) : M name :=
    trace.map (fun n =>
       match translation_unit.resolve_value tu n with
       | None => n
       | Some n => n
       end) $ resolveN n.
End resolve.

Succeed Example _1 :
  let tu := empty_tu abi.abi_default in
  trace.runO (resolveValue tu "test(int& &)") = Some ("test(int&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := empty_tu abi.abi_default in
  trace.runO (resolveValue tu "test(int&& &)") = Some ("test(int&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := empty_tu abi.abi_default in
  trace.runO (resolveValue tu "test(int& &&)") = Some ("test(int&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := empty_tu abi.abi_default in
  trace.runO (resolveValue tu "test(int&& &&)") = Some ("test(int&&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := empty_tu abi.abi_default in
  trace.runO (resolveValue tu "test(const int)") = Some ("test(int)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := empty_tu abi.abi_default in
  trace.runO (resolveValue tu "test(volatile int, const int&)") = Some ("test(int, const int&)"%cpp_name) := eq_refl.

Succeed Example _vec_alias_canon :
  let tu0 := empty_tu abi.abi_default in
  let tu :=
    {| types := <[ Nglobal (Nid "v4di_u") := Gtypedef (Tvector Tlonglong 4 1) ]> tu0.(types)
     ; symbols := tu0.(symbols)
     ; namespace_aliases := tu0.(namespace_aliases)
     ; initializer := tu0.(initializer)
     ; asserts := tu0.(asserts)
     ; abi := tu0.(abi)
     ; msymbols := tu0.(msymbols)
     ; mtypes := tu0.(mtypes)
     ; maliases := tu0.(maliases)
     ; minstances := tu0.(minstances) |} in
  trace.runO (resolveValue tu (Nglobal (Nfunction function_qualifiers.N "f" [Tptr (Tconst (Tnamed (Nglobal (Nid "v4di_u"))))]))) =
    Some (Nglobal (Nfunction function_qualifiers.N "f" [Tptr (Tconst (Tvector Tlonglong 4 32))])) := eq_refl.
