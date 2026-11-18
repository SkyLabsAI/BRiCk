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
validates the offsets of the virtual bases, and the alignment of every base
subobject. The rules give each object of class type a pointer aligned to
the full alignment of its class ([align_of], see [has_type_ptr']), also at
base subobjects, where C++ only guarantees the alignment of the base's
non-virtual part (see [doc/cpp/alignof.md]). So every base, virtual or
not, must sit at an offset aligned to its class's full alignment, as cpp2v
also requires.
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

(** [class_align tu b] is the full alignment of class [b], when it is
valid: what [align_of (Tnamed b)] is under [tu ⊧ σ], and so the alignment
the rules assume for every pointer to a [b], also at a base subobject. *)
Definition class_align (tu : translation_unit) (b : globname) : option N :=
  match tu.(types) !! b with
  | Some (Gstruct _ as g) => GlobDecl_valid_align_of g
  | Some (Gvstruct vs) => if vstruct_nv_ok vs then Some vs.(vs_struct).(s_alignment) else None
  | _ => None
  end.

(** [nv_bases tu b] are the non-virtual bases of class [b]. *)
Definition nv_bases (tu : translation_unit) (b : globname) : option (list (classname * LayoutInfo)) :=
  match tu.(types) !! b with
  | Some (Gstruct st) => Some st.(s_bases)
  | Some (Gvstruct vs) => Some vs.(vs_struct).(s_bases)
  | _ => None
  end.

(**
[bases_aligned tu fuel al bases] checks that each base in [bases] of an
object aligned to [al] sits at an offset aligned to the base's full
alignment ([class_align]), which divides [al], and recursively that the
same holds for the non-virtual bases of each base. So, if the object is
[al]-aligned, every base subobject reached through non-virtual bases is
aligned as the rules assume. The virtual bases of a base are not laid out
by the base, but by the complete object, which checks them in
[vbase_piece].
*)
Fixpoint bases_aligned (tu : translation_unit) (fuel : nat) (al : N)
    (bases : list (classname * LayoutInfo)) : bool :=
  match fuel with
  | O => false
  | S fuel =>
    forallb (fun b =>
      match li_bytes b.2 , class_align tu b.1 , nv_bases tu b.1 with
      | Some off , Some bal , Some bbases =>
        bool_decide ((Z.of_N bal | off) /\ (bal | al)%N) && bases_aligned tu fuel bal bbases
      | _ , _ , _ => false
      end) bases
  end.

(** The alignment that a virtual base [b] needs, and the size it must
have room for. The alignment is its full alignment ([class_align]), which
the rules assume for its pointer. For a class without virtual bases, the
size is its size: once constructed, its [Rep] may claim [type_ptr], which
covers [size_of] bytes. For a class with virtual bases, it is nothing
beyond its data. *)
Definition vbase_req (tu : translation_unit) (b : globname) : option (N * N) :=
  match tu.(types) !! b with
  | Some (Gstruct s as g) => (fun al => (al, s.(s_size))) <$> GlobDecl_valid_align_of g
  | Some (Gvstruct vs) => if vstruct_nv_ok vs then Some (vs.(vs_struct).(s_alignment), 0%N) else None
  | _ => None
  end.

(** The data [[offset, data end)] of a virtual base [b] of a complete
object of [size] bytes aligned to [align]; its own non-virtual bases must
be aligned too ([bases_aligned]). *)
Definition vbase_piece (tu : translation_unit) (size align : Z) (b : classname * LayoutInfo)
    : option (Z * Z) :=
  match li_bytes b.2 , class_data tu vstruct_layout_fuel b.1 , vbase_req tu b.1 , nv_bases tu b.1 with
  | Some o , Some d , Some (al, sz) , Some bbases =>
    if bool_decide (0 <= d /\ o + Z.max d (Z.of_N sz) <= size /\ (Z.of_N al | o) /\ (Z.of_N al | align))
       && bases_aligned tu vstruct_layout_fuel al bbases
    then Some (o, o + d) else None
  | _ , _ , _ , _ => None
  end.

(**
[vstruct_layout_ok tu cls vs] validates the layout of a complete object
of class [cls], whose body is [vs]: its alignments are valid, its virtual
bases are distinct and lie inside the object at offsets aligned as their
[vbase_req] requires, every base subobject reached through non-virtual
bases is aligned to its class's full alignment ([bases_aligned]), and the
data of its pieces (the virtual bases and the non-virtual part) are
pairwise disjoint.
*)
Definition vstruct_layout_ok (tu : translation_unit) (cls : globname) (vs : VStruct) : bool :=
  let fuel := vstruct_layout_fuel in
  let size := Z.of_N vs.(vs_struct).(s_size) in
  let align := Z.of_N vs.(vs_struct).(s_alignment) in
  vstruct_nv_ok vs &&
  bool_decide (NoDup (List.map fst vs.(vs_vbases))) &&
  bases_aligned tu fuel vs.(vs_struct).(s_alignment) vs.(vs_struct).(s_bases) &&
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

  Lemma class_align_sub b al : class_align tu b = Some al -> class_align tu' b = Some al.
  Proof using Hsub.
    rewrite /class_align. case H: (tu.(types) !! b) => [[]|] //.
    - by rewrite (sub_module_preserves_gstruct _ _ _ _ Hsub H).
    - by rewrite (sub_module_preserves_gvstruct _ _ _ _ Hsub H).
  Qed.

  Lemma nv_bases_sub b bs : nv_bases tu b = Some bs -> nv_bases tu' b = Some bs.
  Proof using Hsub.
    rewrite /nv_bases. case H: (tu.(types) !! b) => [[]|] //.
    - by rewrite (sub_module_preserves_gstruct _ _ _ _ Hsub H).
    - by rewrite (sub_module_preserves_gvstruct _ _ _ _ Hsub H).
  Qed.

  Lemma bases_aligned_sub fuel al bases :
    bases_aligned tu fuel al bases = true -> bases_aligned tu' fuel al bases = true.
  Proof using Hsub.
    revert al bases. induction fuel as [|fuel IH] => al bases //=.
    rewrite !forallb_forall => Hall b Hb. move: (Hall b Hb).
    case: (li_bytes b.2) => // off.
    case E1: (class_align tu b.1) => [bal|] //.
    case E2: (nv_bases tu b.1) => [bbases|] //.
    rewrite (class_align_sub _ _ E1) (nv_bases_sub _ _ E2).
    move=> /andb_prop [-> /IH ->]. done.
  Qed.

  Lemma vbase_piece_sub size align b r :
    vbase_piece tu size align b = Some r -> vbase_piece tu' size align b = Some r.
  Proof using Hsub.
    rewrite /vbase_piece.
    destruct (li_bytes b.2) as [o|]; last done.
    destruct (class_data tu vstruct_layout_fuel b.1) as [d|] eqn:E1; last done.
    destruct (vbase_req tu b.1) as [[al sz]|] eqn:E2; last done.
    destruct (nv_bases tu b.1) as [bbases|] eqn:E3; last done.
    rewrite (class_data_sub _ _ _ E1) (vbase_req_sub _ _ E2) (nv_bases_sub _ _ E3).
    destruct (bases_aligned tu vstruct_layout_fuel al bbases) eqn:E4.
    - by rewrite (bases_aligned_sub _ _ _ E4).
    - by rewrite andb_false_r.
  Qed.

  Lemma vstruct_layout_ok_sub cls vs :
    vstruct_layout_ok tu cls vs = true -> vstruct_layout_ok tu' cls vs = true.
  Proof using Hsub.
    rewrite /vstruct_layout_ok.
    destruct (bases_aligned tu _ _ _) eqn:Eal; last by rewrite andb_false_r.
    rewrite (bases_aligned_sub _ _ _ Eal) !andb_true_r.
    destruct (mapM (vbase_piece tu _ _) vs.(vs_vbases)) as [pieces|] eqn:Ep;
      last by rewrite andb_false_r.
    destruct (class_data tu _ cls) as [nv|] eqn:En; last by rewrite andb_false_r.
    have -> : mapM (vbase_piece tu' (Z.of_N vs.(vs_struct).(s_size))
                (Z.of_N vs.(vs_struct).(s_alignment))) vs.(vs_vbases) = Some pieces.
    { apply: (mapM_impl _ _ _ _ _ Ep). intros b y. apply vbase_piece_sub. }
    by rewrite (class_data_sub _ _ _ En).
  Qed.
End sub_module.
