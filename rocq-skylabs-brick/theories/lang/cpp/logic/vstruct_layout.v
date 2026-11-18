(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Layout checks for classes with virtual bases

The rules that construct and destroy a complete object of a class with
virtual bases ([wp_init_complete_vstruct] and [wp_destroy_vstruct]) hand
out storage for its pieces: a [tblockR] or [nv_tblockR] for each virtual
base, then an [nv_tblockR] for the non-virtual part, and, inside each
piece, storage for its non-virtual bases and its fields. A rule that
handed out storage overlapping resources the caller already holds would
be vacuous, so the rules check the layout first.

Storage at class types is abstract ([tblockR] in [heap_pred/block.v],
[nv_tblockR] in [heap_pred/vbase.v]): it is what an object owns wherever
it sits, and a potentially-overlapping subobject does not own its tail
padding. Nothing turns it into bytes, so a destructor that returns it,
even one called explicitly, returns nothing that another piece holds. We
bound what the storage of a piece may cover by its _data_: the prefix up
to the end of its last field, its vptr, or the data of its last
non-virtual base. Interior padding is data; tail padding is not. The data
of a piece includes that of its non-virtual bases and fields, so it
covers everything handed out while constructing or destroying the piece.

The check below therefore requires the data of the pieces to be pairwise
disjoint. A piece may occupy the tail padding of another, and an empty
class (without fields, virtual functions or virtual bases) may overlap any
piece. Sharing a vptr is rejected: a class with virtual bases always has
one, at offset 0.

Layout metadata is untrusted (see [valid_alignment]): the check also
validates offsets and alignment of the virtual bases.
*)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.

#[local] Open Scope Z_scope.

(**
[vstruct_nv_ok vs] validates the alignments of a class with virtual
bases: the alignment of a complete object is valid for its size (so
[align_of] is [s_alignment], see [GlobDecl_valid_align_of]), and the
alignment of the non-virtual part is a power of two that divides it.
Without the first check, a TU claiming alignment 0 would let the rules
hand out [alignedR] facts that no allocation satisfies.
*)
Definition vstruct_nv_ok (vs : VStruct) : bool :=
  bool_decide (valid_alignment vs.(vs_struct).(s_size) vs.(vs_struct).(s_alignment)) &&
  bool_decide (valid_alignment vs.(vs_struct).(s_alignment) vs.(vs_nv_alignment)).

(**
[tu_size_of tu t] is the size of [t] as far as [tu] determines it
(member pointers, whose size the [genv] fixes, are unknown). It agrees
with [size_of] under [tu ⊧ σ], and is only used to bound the data of a
class: [None] makes the bound conservative.
*)
Fixpoint tu_size_of (tu : translation_unit) (t : type) : option N :=
  match t with
  | Tptr _ | Tref _ | Trv_ref _ | Tnullptr =>
    Some (bitsize.bytesN (abi.pointer_size_bitsize tu.(abi)))
  | Tnum sz _ => Some (int_rank.bytesN sz)
  | Tchar_ ct => Some (char_type.bytesN ct)
  | Tvoid | Tbool => Some 1%N
  | Tarray t n => N.mul n <$> tu_size_of tu t
  | Tnamed nm | Tenum nm => tu.(types) !! nm ≫= GlobDecl_size_of
  | Tqualified _ t => tu_size_of tu t
  | Tfloat_ sz => Some (float_type.bytesN sz)
  | Tarch sz _ => bitsize.bytesN <$> sz
  | _ => None
  end.

(** The offset, in bytes, of a base or field; [None] unless it is a whole byte. *)
Definition li_bytes (li : LayoutInfo) : option Z :=
  if bool_decide ((8 | li.(li_offset)) /\ 0 <= li.(li_offset))
  then Some (li.(li_offset) / 8) else None.

(**
[struct_data tu rec st vptr = Some data] says that a subobject with body
[st] constructed without its virtual bases (a complete object of a class
without virtual bases, or the non-virtual part of a class with virtual
bases) has its data in [[0, data)], relative to its start: its fields,
its vptr if [vptr], and the data of its non-virtual bases (given by
[rec]), with any padding between them.
*)
Definition base_data (rec : globname -> option Z) (b : classname * LayoutInfo) : option Z :=
  match li_bytes b.2 , rec b.1 with
  | Some off , Some d => Some (off + d)
  | _ , _ => None
  end.

Definition field_end (tu : translation_unit) (m : Member) : option Z :=
  match li_bytes m.(mem_layout) , tu_size_of tu m.(mem_type) with
  | Some off , Some sz => Some (off + Z.of_N sz)
  | _ , _ => None
  end.

Definition struct_data (tu : translation_unit) (rec : globname -> option Z)
    (st : Struct) (vptr : bool) : option Z :=
  let ptr := Z.of_N (bitsize.bytesN (abi.pointer_size_bitsize tu.(abi))) in
  match mapM (base_data rec) st.(s_bases) , mapM (field_end tu) st.(s_fields) with
  | Some bases , Some fields => Some (foldr Z.max (if vptr then ptr else 0) (bases ++ fields))
  | _ , _ => None
  end.

(** [class_data tu fuel cls] is [struct_data] for class [cls]. The fuel
bounds the height of the hierarchy. *)
Fixpoint class_data (tu : translation_unit) (fuel : nat) (cls : globname) : option Z :=
  match fuel with
  | O => None
  | S fuel =>
    match tu.(types) !! cls with
    | Some (Gstruct st) => struct_data tu (class_data tu fuel) st (has_vtable st)
    | Some (Gvstruct vs) =>
      (* A class with virtual bases always has a vptr. *)
      struct_data tu (class_data tu fuel) vs.(vs_struct) true
    | _ => None
    end
  end.

(** A fixed fuel, rather than one computed from the translation unit,
keeps the check monotone along [sub_module]. *)
Definition vstruct_layout_fuel : nat := 256.

(** [x] and [y] are disjoint ranges [[lo, hi)] (an empty range is
disjoint from any range). *)
Definition ranges_disjoint (x y : Z * Z) : bool :=
  bool_decide (x.2 <= y.1 \/ y.2 <= x.1 \/ x.2 <= x.1 \/ y.2 <= y.1).

(** The ranges [rs] are pairwise disjoint. *)
Fixpoint ranges_pairwise_disjoint (rs : list (Z * Z)) : bool :=
  match rs with
  | nil => true
  | r :: rs => forallb (ranges_disjoint r) rs && ranges_pairwise_disjoint rs
  end.

(** The alignment that a virtual base [b] needs, and the size it must
have room for. For a class without virtual bases, these are its
alignment and size: once constructed, its [Rep] may claim [type_ptr],
which covers [size_of] bytes. For a class with virtual bases, they are
the alignment of its non-virtual part (which its fields' and bases'
alignments divide) and nothing beyond its data. *)
Definition vbase_req (tu : translation_unit) (b : globname) : option (N * N) :=
  match tu.(types) !! b with
  | Some (Gstruct s as g) => (fun al => (al, s.(s_size))) <$> GlobDecl_valid_align_of g
  | Some (Gvstruct vs) => if vstruct_nv_ok vs then Some (vs.(vs_nv_alignment), 0%N) else None
  | _ => None
  end.

(** The data [[offset, data end)] of a virtual base [b] of a complete
object of [size] bytes aligned to [align]. *)
Definition vbase_piece (tu : translation_unit) (size align : Z) (b : classname * LayoutInfo)
    : option (Z * Z) :=
  match li_bytes b.2 , class_data tu vstruct_layout_fuel b.1 , vbase_req tu b.1 with
  | Some o , Some d , Some (al, sz) =>
    if bool_decide (0 <= d /\ o + Z.max d (Z.of_N sz) <= size /\ (Z.of_N al | o) /\ (Z.of_N al | align))
    then Some (o, o + d) else None
  | _ , _ , _ => None
  end.

(**
[vstruct_layout_ok tu cls vs] validates the layout of a complete object
of class [cls], whose body is [vs]: its alignments are valid, its virtual
bases are distinct, lie inside the object at offsets aligned as their
[vbase_req] requires, and the data of its pieces (the virtual bases and the
non-virtual part) are pairwise disjoint.
*)
Definition vstruct_layout_ok (tu : translation_unit) (cls : globname) (vs : VStruct) : bool :=
  let fuel := vstruct_layout_fuel in
  let size := Z.of_N vs.(vs_struct).(s_size) in
  let align := Z.of_N vs.(vs_struct).(s_alignment) in
  vstruct_nv_ok vs &&
  bool_decide (NoDup (List.map fst vs.(vs_vbases))) &&
  match mapM (vbase_piece tu size align) vs.(vs_vbases) , class_data tu fuel cls with
  | Some pieces , Some nv => bool_decide (nv <= size) && ranges_pairwise_disjoint ((0, nv) :: pieces)
  | _ , _ => false
  end.

(** ** The check is monotone along [sub_module] *)

Lemma mapM_impl {A B} (f g : A -> option B) (l : list A) (r : list B) :
  (forall x y, f x = Some y -> g x = Some y) ->
  mapM f l = Some r -> mapM g l = Some r.
Proof.
  intros Hfg. revert r. induction l as [|x l IHl] => r /=; first done.
  destruct (f x) as [y|] eqn:E => //=. rewrite (Hfg _ _ E) /=.
  destruct (mapM f l) as [ys|] eqn:E2 => //=. by rewrite (IHl ys eq_refl).
Qed.

Section sub_module.
  Context {tu tu' : translation_unit} (Hsub : sub_module tu tu').

  Lemma GlobDecl_size_of_sub gn sz :
    tu.(types) !! gn ≫= GlobDecl_size_of = Some sz ->
    tu'.(types) !! gn ≫= GlobDecl_size_of = Some sz.
  Proof using Hsub.
    case H: (tu.(types) !! gn) => [g|] //= Hg.
    have [g' [-> Hle]] := types_compat _ _ Hsub gn g H.
    exact: (proj1 (Roption_leq_eq_equiv (R:=eq)) (proper_GlobDecl_size_of _ _ Hle)).
  Qed.

  Lemma tu_size_of_sub t r : tu_size_of tu t = Some r -> tu_size_of tu' t = Some r.
  Proof using Hsub.
    have Habi := abi_compat _ _ Hsub.
    revert r. induction t; intros res; cbn; rewrite ?Habi; try done.
    - destruct (tu_size_of tu t) eqn:E; cbn; last done. by rewrite (IHt _ eq_refl).
    - apply GlobDecl_size_of_sub.
    - apply GlobDecl_size_of_sub.
    - apply IHt.
  Qed.

  Lemma struct_data_sub rec rec' st vptr d :
    (forall c x, rec c = Some x -> rec' c = Some x) ->
    struct_data tu rec st vptr = Some d ->
    struct_data tu' rec' st vptr = Some d.
  Proof using Hsub.
    intros Hrec. rewrite /struct_data -(abi_compat _ _ Hsub).
    destruct (mapM (base_data rec) _) as [bases|] eqn:Eb; last done.
    destruct (mapM (field_end tu) _) as [fields|] eqn:Ef; last done.
    have -> : mapM (base_data rec') st.(s_bases) = Some bases.
    { apply: (mapM_impl _ _ _ _ _ Eb). intros b y. rewrite /base_data.
      case: (li_bytes b.2) => // off.
      case E: (rec b.1) => [d'|] //. by rewrite (Hrec _ _ E). }
    have -> : mapM (field_end tu') st.(s_fields) = Some fields.
    { apply: (mapM_impl _ _ _ _ _ Ef). intros m y. rewrite /field_end.
      case: (li_bytes _) => // off.
      case E: (tu_size_of tu _) => [sz|] //. by rewrite (tu_size_of_sub _ _ E). }
    done.
  Qed.

  Lemma class_data_sub fuel cls d :
    class_data tu fuel cls = Some d -> class_data tu' fuel cls = Some d.
  Proof using Hsub.
    revert cls d. induction fuel as [|fuel IH] => cls d //=.
    case H: (tu.(types) !! cls) => [[]|] //.
    - rewrite (sub_module_preserves_gstruct _ _ _ _ Hsub H).
      by apply struct_data_sub.
    - rewrite (sub_module_preserves_gvstruct _ _ _ _ Hsub H).
      by apply struct_data_sub.
  Qed.

  Lemma vbase_req_sub b r : vbase_req tu b = Some r -> vbase_req tu' b = Some r.
  Proof using Hsub.
    rewrite /vbase_req. case H: (tu.(types) !! b) => [[]|] //.
    - by rewrite (sub_module_preserves_gstruct _ _ _ _ Hsub H).
    - by rewrite (sub_module_preserves_gvstruct _ _ _ _ Hsub H).
  Qed.

  Lemma vstruct_layout_ok_sub cls vs :
    vstruct_layout_ok tu cls vs = true -> vstruct_layout_ok tu' cls vs = true.
  Proof using Hsub.
    rewrite /vstruct_layout_ok.
    destruct (mapM (vbase_piece tu _ _) vs.(vs_vbases)) as [pieces|] eqn:Ep;
      last by rewrite andb_false_r.
    destruct (class_data tu _ cls) as [nv|] eqn:En; last by rewrite andb_false_r.
    have -> : mapM (vbase_piece tu' (Z.of_N vs.(vs_struct).(s_size))
                (Z.of_N vs.(vs_struct).(s_alignment))) vs.(vs_vbases) = Some pieces.
    { apply: (mapM_impl _ _ _ _ _ Ep). intros b y. rewrite /vbase_piece.
      case: (li_bytes b.2) => // o.
      case E1: (class_data tu _ b.1) => [d'|] //.
      case E2: (vbase_req tu b.1) => [[al sz]|] //.
      by rewrite (class_data_sub _ _ _ E1) (vbase_req_sub _ _ E2). }
    by rewrite (class_data_sub _ _ _ En).
  Qed.
End sub_module.
