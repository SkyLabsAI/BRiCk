(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Ltac2.Ltac2.
Require Export bluerock.prelude.base.	(* for, e.g., <<::>> *)
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Require Import bluerock.prelude.parray.
Require Import bluerock.prelude.uint63.
Require Export Stdlib.Strings.PrimString.
Require Import bluerock.prelude.avl.
Require Export bluerock.lang.cpp.syntax. (* NOTE: too much *)
Require bluerock.lang.cpp.semantics.sub_module.
Require Export bluerock.lang.cpp.parser.stmt.
Require Import bluerock.lang.cpp.parser.lang.
Require Import bluerock.lang.cpp.parser.type.
Require Import bluerock.lang.cpp.parser.name.
Require Import bluerock.lang.cpp.parser.expr.
Require Import bluerock.lang.cpp.parser.decl.
Require Import bluerock.lang.cpp.parser.notation.
Require Import bluerock.lang.cpp.parser.reduction.

Include ParserName.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Module Import translation_unit.

  (* Sort and remove duplicates
     Doing both of these operations at the same time is more efficient than
     doing them separately. Since this is computed on TUs, performance may
     be important.
   *)
  Module sort.
    Fixpoint insert (x : name) (ls : list name) : list name :=
      match ls with
      | nil => x :: nil
      | l :: ls' =>
          match compare.compareN x l with
          | Lt => x :: ls
          | Eq => ls
          | Gt => l :: insert x ls'
          end
      end.
    Fixpoint sort (ls : list name) : list name :=
      match ls with
      | nil => nil
      | l :: ls => insert l $ sort ls
      end.
  End sort.

  (**
  We work with an exploded [translation_unit] and raw trees for
  efficiency.
  *)

  Definition raw_symbol_table : Type := NM.Raw.t ObjValue.
  Definition raw_type_table : Type := NM.Raw.t GlobDecl.
  Definition raw_alias_table : Type := NM.Raw.t (list name).

  #[global] Instance raw_structured_insert : forall {T}, Insert globname T (NM.Raw.t T) := _.

  Definition dup_info := list (name * (GlobDecl + ObjValue)).
  (** This representation is isomorphic to [translation_unit * list name] as shown by [decls]. *)
  Definition t : Type :=
    raw_symbol_table -> raw_type_table -> list name -> raw_alias_table -> dup_info ->
    (raw_symbol_table -> raw_type_table -> list name -> raw_alias_table -> dup_info -> translation_unit * dup_info) ->
    translation_unit * dup_info.

  Definition merge_obj_value (a b : ObjValue) : option ObjValue :=
    if sub_module.ObjValue_le a b then
      Some b
    else if sub_module.ObjValue_le b a then Some a
         else None.

  (** Constructs a [translation_unit.t] with _one_ symbol, mapping [n] to [v]. *)
  Definition _symbols (n : name) (v : ObjValue) : t :=
    fun s t ga a dups k =>
      match s !! n with
      | None => k (<[n := v]> s) t ga a dups
      | Some v' => match merge_obj_value v v' with
                  | Some v => k (<[n:=v]> s) t ga a dups
                  | None => k s t ga a ((n, inr v) :: (n, inr v') :: dups)
                  end
      end.
  Definition merge_glob_decl (a b : GlobDecl) : option GlobDecl :=
    if sub_module.GlobDecl_le a b then
      Some b
    else if sub_module.GlobDecl_le b a then Some a
         else None.

  (** Constructs a [translation_unit.t] with _one_ type, mapping [n] to [v]. *)
  Definition _types (n : name) (v : GlobDecl) : t :=
    fun s t ga a dups k =>
      if bool_decide (Gtypedef (Tnamed n) = v \/ Gtypedef (Tenum n) = v)
      then
        (* ignore self-aliases. These arise when you do
           something like
           <<
           typedef enum memory_order { .. } memory_order;
           >>
         *)
        k s t ga a dups
      else
        match t !! n with
        | None => k s (<[n := v]> t) ga a dups
        | Some v' => match merge_glob_decl v v' with
                    | Some v => k s (<[n:=v]> t) ga a dups
                    | None => k s t ga a ((n, inl v) :: (n, inl v') :: dups)
                    end
        end.

  Definition _type_alias (n : name) (ty : type) : t :=
    _types n (Gtypedef ty).

  Definition _value_alias (n : name) (canon : name) : t :=
    fun s t ga a dups k =>
      match a !! n with
      | None => k s t ga (<[n := canon :: nil]> a) dups
      | Some canon' => k s t ga (<[n := canon :: canon']> a) dups
      end.

  Definition _global_alias (canon : name) : t :=
    fun s t ga a dups k => k s t (canon :: ga) a dups.

  (** Constructs an empty [translation_unit.t]. *)
  Definition _skip : t :=
    fun s t ga a dups k => k s t ga a dups.

  Fixpoint array_fold {A B}
    (f : A -> B -> B) (ar : PArray.array A) (fuel : nat) (i : PrimInt63.int) (acc : B) : B :=
    match fuel with
    | 0 => acc
    | S fuel =>
        array_fold f ar fuel (PrimInt63.add i 1) (f (PArray.get ar i) acc)
    end.

  Definition abi_type := endian.

  Definition decls' (ds : PArray.array t) : t :=
    array_fold (fun (X Y : t) s t ga a dups K => X s t ga a dups (fun s t ga a dups => Y s t ga a dups K))
      ds
      (Z.to_nat (Uint63.to_Z (PArray.length ds))) 0%uint63
      (fun s t ga a dups k => k s t ga a dups).

  Definition decls (ds : PArray.array t) (e : abi_type) : translation_unit * dup_info :=
    decls' ds ∅ ∅ [] ∅ [] $ fun s t ga a => pair {|
      symbols := NM.from_raw s;
      types := NM.from_raw t;
      namespace_aliases := (Listset (sort.sort ga), NM.from_raw $ NM.Raw.map (fun x => Listset $ sort.sort x) a);
      initializer := nil;	(** TODO *)
      byte_order := e;
    |}.

  Definition list_decls (ls : list translation_unit.t) :=
    decls $ PArray.of_list _skip ls.

  Module make.
    Import Ltac2.Ltac2.

    Ltac2 Type exn ::= [DuplicateSymbols (constr)].

    (* [check_translation_unit tu]
     *)
    Ltac2 check_translation_unit (tu : preterm) (en : preterm) :=
      let endian := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(endian)) en in
      let tu := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(PArray.array t)) tu in
      let term := Constr.Unsafe.make (Constr.Unsafe.App ('decls) (Array.of_list [tu; endian])) in
      let rtu := Std.eval_vm None term in
      lazy_match! rtu with
      | pair ?tu nil => Std.exact_no_check tu
      | pair _ ?dups =>
          let _ := Message.print (Message.concat (Message.of_string "Duplicate symbols found in translation unit: ") (Message.of_constr dups)) in
          Control.throw (DuplicateSymbols dups)
      end.

  End make.

  Notation check tu en :=
    ltac2:(translation_unit.make.check_translation_unit tu en) (only parsing).

End translation_unit.
Export translation_unit(decls).
#[local] Notation K := translation_unit.t (only parsing).

Definition Dvariable (n : obj_name) (t : type) (init : global_init.t) : K :=
  _symbols n $ Ovar t init.

Definition Dfunction (n : obj_name) (f : Func) : K :=
  _symbols n $ Ofunction f.

Definition Dmethod (n : obj_name) (static : bool) (f : Method) : K :=
  _symbols n $ if static then Ofunction $ static_method f else Omethod f.

Definition Dconstructor (n : obj_name) (f : Ctor) : K :=
  _symbols n $ Oconstructor f.

Definition Ddestructor (n : obj_name) (f : Dtor) : K :=
  _symbols n $ Odestructor f.

Definition Dtype (n : globname) : K :=
  _types n $ Gtype.

Definition Dunsupported (n : globname) (msg : PrimString.string) : K :=
  _types n $ Gunsupported msg.

Definition Dstruct (n : globname) (f : option Struct) : K :=
  _types n $ if f is Some f then Gstruct f else Gtype.

Definition Dunion (n : globname) (f : option Union) : K :=
  _types n $ if f is Some f then Gunion f else Gtype.

Definition Denum (n : globname) (u : type) (cs : list ident) : K :=
  _types n $ Genum u cs.

Definition Denum_constant (n : globname)
    (gn : globname) (ut : exprtype) (v : N + Z) (init : option Expr) : K :=
  _types n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Gconstant t $ Some $ Ecast (Cintegral t) v.

Definition Dtypedef (n : globname) (t : type) : K :=
  _type_alias n t.

Definition Dinline_namespace (ns : name) (child : ident) : K :=
  _value_alias ns (Nscoped ns (Nid child)).

Definition Dusing_namespace (alias : name) (canonical : name) : K :=
  _value_alias alias canonical.

Definition Dglobal_using_namespace (alias : name) : K :=
  _global_alias alias.

Definition Dstatic_assert (msg : option PrimString.string) (e : Expr) : K :=
  _skip.

Definition Qconst_volatile : type -> type := tqualified QCV.
Definition Qconst : type -> type := tqualified QC.
Definition Qvolatile : type -> type := tqualified QV.
