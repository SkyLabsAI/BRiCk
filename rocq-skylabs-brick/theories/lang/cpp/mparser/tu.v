(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.mparser.prelude.
Require Import bluerock.lang.cpp.syntax.translation_unit.
Require Import bluerock.lang.cpp.syntax.namemap.
Require Import bluerock.lang.cpp.syntax.untemp.
Require Export bluerock.lang.cpp.syntax.decl.
Require Export bluerock.lang.cpp.syntax.decl.


(** ** Template-only top-level declarations emitted by cpp2v *)

Module Import Mtranslation_unit.

  (**
  We work with an exploded [Mtranslation_unit] and raw trees for
  efficiency.
  *)

  Definition raw_symbol_table : Type := TM.Raw.tree (template MObjValue).
  Definition raw_type_table : Type := TM.Raw.tree (template MGlobDecl).
  Definition raw_alias_table : Type := TM.Raw.tree (template Mtype).
  Definition raw_instance_table : Type := NM.Raw.tree Mtpreinst.
  (* Definition raw_name_table : Type := TM.Raw.tree Mname. *)

  Definition t : Type :=
    raw_symbol_table -> raw_type_table -> raw_alias_table -> raw_instance_table -> (* raw_name_table -> *)
    (raw_symbol_table -> raw_type_table -> raw_alias_table -> raw_instance_table -> (* raw_name_table -> *) Mtranslation_unit) ->
    Mtranslation_unit.

  Definition _symbols (f : raw_symbol_table -> raw_symbol_table) : t :=
    fun s t a i k => k (f s) t a i.
  Definition _types (f : raw_type_table -> raw_type_table) : t :=
    fun s t a i k => k s (f t) a i.
  Definition _aliases (f : raw_alias_table -> raw_alias_table) : t :=
    fun s t a i k => k s t (f a) i.
  Definition _instances (f : raw_instance_table -> raw_instance_table) : t :=
    fun s t a i k => k s t a (f i).
(*
  Definition _names (f : raw_name_table -> raw_name_table) : t :=
    fun s t a i n k => k s t a i (f n).
 *)
  Definition _skip : t :=
    fun s t a i k => k s t a i.

  Fixpoint decls' (ds : list t) : t :=
    match ds with
    | nil => fun s t a i k => k s t a i
    | d :: ds => fun s t a i k => d s t a i (fun s t a i => decls' ds s t a i k)
    end.

  (**
  TODO: Do we still need <<map_canon>>?
  *)
  Definition decls (ds : list t) : Mtranslation_unit :=
    decls' ds ∅ ∅ ∅ ∅ $ fun s t a i => {|
      msymbols := TM.from_raw s;
      mtypes := TM.from_raw t;
      maliases := TM.from_raw a;
      minstances := NM.from_raw i;
    |}.

End Mtranslation_unit.
#[local] Notation K := Mtranslation_unit.t (only parsing).

#[local] Notation Mtemp_params := (list Mtemp_param).

Definition Dvariable (ps : Mtemp_params) (n : Mname) (t : Mtype) (init : global_init.t) : K :=
  _symbols <[n := Template ps $ Ovar t init]>.

Definition Dfunction (ps : Mtemp_params) (n : Mname)  (f : MFunc) : K :=
  _symbols <[n := Template ps $ Ofunction f]>.

Definition Dmethod (ps : Mtemp_params) (n : Mname) (static : bool) (f : MMethod) : K :=
  _symbols <[n := Template ps $ if static then Ofunction $ static_method f else Omethod f]>.

Definition Dconstructor (ps : Mtemp_params) (n : Mname) (f : MCtor) : K :=
  _symbols <[n := Template ps $ Oconstructor f]>.

Definition Ddestructor (ps : Mtemp_params) (n : Mname) (f : MDtor) : K :=
  _symbols <[n := Template ps $ Odestructor f]>.

Definition Dtype (ps : Mtemp_params) (n : Mname) : K :=
  _types <[n := Template ps Gtype]>.

Definition Dstruct (ps : Mtemp_params) (n : Mname) (f : option MStruct) : K :=
  _types <[n := Template ps $ if f is Some f then Gstruct f else Gtype]>.

Definition Dunion (ps : Mtemp_params) (n : Mname) (f : option MUnion) : K :=
  _types <[n := Template ps $ if f is Some f then Gunion f else Gtype]>.

Definition Denum (ps : Mtemp_params) (n : Mname) (u: Mtype) (cs : list ident) : K :=
  _types <[n := Template ps $ Genum u cs]>.

Definition Denum_constant (ps : Mtemp_params) (n : Mname)
    (gn : Mglobname) (ut : Mexprtype) (v : N + Z) (init : option MExpr) : K :=
  _types $ insert n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Template ps $ Gconstant t $ Some $ Ecast (Cintegral t) v.

Definition Dtypedef (ps : Mtemp_params) (n : Mname) (t : Mtype) : K :=
  _aliases <[n := Template ps t]>.

Definition Dstatic_assert (msg : option bs) (e : MExpr) : K :=
  _skip.

(* TODO?: the [c : Mname] argument should actually be a [name], but the parser
   setup that we have causes it to be inferred as an [Mname]. To get around this,
   we accept an [Mname] and then convert it into a [name]. *)
Definition Dinstantiation (c : Mname) (t : Mname) (xs : list Mtemp_arg) : K :=
  match trace.run $ untempN c with
  | inl _ => _skip
  | inr c =>
      _instances <[c := templates.TPreInst t xs]>
  end.

Definition Dname (m : Mname) (n : Mname) : K :=
  _skip. (* _names <[m := n]>. *)
