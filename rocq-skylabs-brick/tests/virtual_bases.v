(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Classes with virtual bases: [Rep]s, and the rules for their
    constructors and destructors, on a diamond.

    Each constructor and destructor has a single specification, which
    covers the non-virtual part of the object and borrows the virtual
    base. Here we check that
    - the constructor and destructor of [G] satisfy theirs
      ([G_ctor_ok], [G_dtor_ok]): the one virtual base is lent to [L],
      taken back, lent to [R], and taken back;
    - a complete [G] can be constructed and destroyed from them
      ([G_complete_ok], [G_destroy_ok]): only there is the virtual base
      constructed and destroyed;
    - what is not supported is stuck (the end of the file). *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.logic.func.
Require Import skylabs.lang.cpp.logic.call.
Require Import skylabs.lang.cpp.logic.vstruct_layout.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{{
struct VB { int v; VB() {} };
struct L : virtual VB { L() {} };
struct R : virtual VB { R() {} };
struct G : L, R { int g; G() {} };
void test() { G g; }
}}}.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Hypothesis Hσ : source ⊧ σ.

  Definition VBR (q : cQp.t) : Rep := _field "VB::v" |-> uninitR Tint q.
  (** A pre-[Rep] owns the vtable pointer ([vptrR]); for [G], also
      those of its non-virtual bases [L] and [R]. *)
  Definition L_pre (q : cQp.t) : Rep := vptrR "L" q.
  Definition LR (q : cQp.t) : Rep := L_pre q ** vbaseR "L" "VB" (VBR q).
  Definition R_pre (q : cQp.t) : Rep := vptrR "R" q.
  Definition RR (q : cQp.t) : Rep := R_pre q ** vbaseR "R" "VB" (VBR q).
  Definition G_pre (q : cQp.t) : Rep :=
    _base "G" "L" |-> L_pre q ** _base "G" "R" |-> R_pre q **
    vptrR "G" q ** _field "G::g" |-> uninitR Tint q.
  Definition GR (q : cQp.t) : Rep := G_pre q ** vbaseR "G" "VB" (VBR q).

  (** A full [Rep] is fractional, although it hides where the virtual
      base is. *)
  #[local] Instance VBR_cfractional : CFractional VBR.
  Proof. rewrite /VBR. apply _. Qed.
  #[local] Instance GR_cfractional : CFractional GR.
  Proof. rewrite /GR /G_pre /L_pre /R_pre. apply _. Qed.

  (* The single specification of a constructor: it borrows the virtual base. *)
  Definition ctor_spec (cls : globname) (cnd : obj_name) (pre post : Rep) : mpred :=
    □ Forall (this : ptr) (Q : ptr -> epred),
      this |-> nv_tblockR cls 1$m ** this |-> pre **
      (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* this |-> post -* Q p)
      -* wp_fptr (type_of_value (Oconstructor
            (Build_Ctor cls nil CC_C Ar_Definite exception_spec.MayThrow None))) (_global cnd) [this] Q.

  Lemma G_ctor_ok (this : ptr) (Q : ptr -> epred) ctor :
    source.(symbols) !! "G::G()"%cpp_name = Some (Oconstructor ctor) ->
    ctor_spec "L" "L::L()" (vbaseR "L" "VB" (VBR 1$m)) (LR 1$m) **
    ctor_spec "R" "R::R()" (vbaseR "R" "VB" (VBR 1$m)) (RR 1$m) **
    this |-> nv_tblockR "G" 1$m ** this |-> vbaseR "G" "VB" (VBR 1$m) **
    (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* this |-> GR 1$m -* Q p)
    |-- wp_ctor source ctor [this] Q.
  Proof using Hσ.
    intros [= <-]. iIntros "(#SL & #SR & B & VB & HQ)".
    iApply wp_ctor_intro. cbn.
    iFrame "B". iModIntro.
    rewrite /wp_vstruct_initializer_list.
    repeat (case_bool_decide; try congruence).
    iIntros "_".
    iDestruct (_at_vbaseR with "VB") as (pvb) "[#V VB]".
    (* [L]: its virtual base is the one of [G]. *)
    iExists pvb. iFrame "V". iIntros "#VL".
    rewrite /wp_base_ctor_call /ctor_fun_type /=.
    do 2 (erewrite glob_def_genv_compat_vstruct; last by vm_compute). cbn.
    rewrite /wp_args /= /nd_seqs /= /wp.WPE.Mret.
    iIntros "!> BL". iApply "SL". iFrame "BL".
    iSplitL "VB". { iApply (vbaseR_intro with "VL VB"). }
    iIntros (p) "Hp L". rewrite /LR _at_sep. iDestruct "L" as "[TL L]".
    rewrite /= !interp_unfold /=. iModIntro. iFrame "Hp". iModIntro.
    (* Take the virtual base back, and lend it to [R]. *)
    iDestruct (vbaseR_elim with "VL L") as "VB".
    iExists pvb. iFrame "V". iIntros "#VR !> BR". iApply "SR". iFrame "BR".
    iSplitL "VB". { iApply (vbaseR_intro with "VR VB"). }
    iIntros (p') "Hp' R". rewrite /RR _at_sep. iDestruct "R" as "[TR R]".
    iModIntro. iFrame "Hp'". iModIntro.
    iDestruct (vbaseR_elim with "VR R") as "VB".
    (* the vtable pointer of [G] is installed after its bases *)
    iIntros "TG".
    (* the field of [G] *)
    default_initialize_unfold. cbn.
    iIntros "Hg !>". rewrite interp_unfold /=. iModIntro.
    (* the body *)
    iApply wp_seq. rewrite wp_block_unfold. iIntros "!> !> !>". cbn.
    iIntros "!> %p0 Hp0". iApply ("HQ" with "Hp0").
    rewrite /GR _at_sep. iSplitR "VB"; last by iApply (vbaseR_intro with "V VB").
    rewrite /G_pre !_at_sep !_at_offsetR. iFrame "TL TR TG Hg".
  Qed.

  (* The single specification of a destructor: it returns the virtual base. *)
  Definition dtor_type (cls : globname) : type :=
    Tmember_func (Tnamed cls) (Tfunction (FunctionType Tvoid nil)).
  Definition dtor_spec (cls : globname) (dnd : obj_name) (pre post : Rep) : mpred :=
    □ Forall (this : ptr) (Q : ptr -> epred),
      this |-> pre **
      (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
         this |-> nv_tblockR cls 1$m -* this |-> post -* Q p)
      -* wp_fptr (dtor_type cls) (_global dnd) [this] Q.

  Lemma G_dtor_ok (this : ptr) (Q : ptr -> epred) dtor :
    source.(symbols) !! "G::~G()"%cpp_name = Some (Odestructor dtor) ->
    dtor_spec "L" "L::~L()" (LR 1$m) (vbaseR "L" "VB" (VBR 1$m)) **
    dtor_spec "R" "R::~R()" (RR 1$m) (vbaseR "R" "VB" (VBR 1$m)) **
    this |-> GR 1$m **
    (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
       this |-> nv_tblockR "G" 1$m -* this |-> vbaseR "G" "VB" (VBR 1$m) -* Q p)
    |-- wp_dtor source dtor [this] Q.
  Proof.
    intros [= <-]. iIntros "(#SL & #SR & G & HQ)".
    iApply wp_dtor_intro. cbn.
    iModIntro. iSplit; first done.
    rewrite /GR /G_pre !_at_sep !_at_offsetR. iDestruct "G" as "((TL & TR & TG & Hg) & VB)".
    iDestruct (_at_vbaseR with "VB") as (pvb) "[#V VB]".
    rewrite /wpd_members /= !interp_unfold /=.
    (* the field of [G] *)
    rewrite (interp_unfold (FreeTemps.delete _ _ _)) /=.
    iApply destroy_val_intro_val; first done. cbn.
    iSplitL "Hg". { iExists Vundef. by rewrite uninitR_tptstoR. }
    rewrite interp_unfold /=. iModIntro.
    (* [R], then [L]: each borrows the virtual base of [G]. *)
    iExists pvb. iFrame "V". iIntros "!> #VR".
    rewrite /wp_base_destructor /wp_mfptr.
    iApply "SR". iSplitL "VB TR".
    { rewrite /RR _at_sep. iFrame "TR". iApply (vbaseR_intro with "VR VB"). }
    iIntros (p) "Hp BR VB". iExists Vvoid. iFrame "Hp BR".
    iDestruct (vbaseR_elim with "VR VB") as "VB".
    iExists pvb. iFrame "V". iIntros "#VL".
    iApply "SL". iSplitL "VB TL".
    { rewrite /LR _at_sep. iFrame "TL". iApply (vbaseR_intro with "VL VB"). }
    iIntros (p') "Hp' BL VB". iExists Vvoid. iFrame "Hp' BL".
    iDestruct (vbaseR_elim with "VL VB") as "VB".
    (* the vtable pointer of [G] goes back with its memory *)
    iFrame "TG". iIntros "BG !> %p0 Hp0". iApply ("HQ" with "Hp0 BG").
    iApply (vbaseR_intro with "V VB").
  Qed.

  (** ** Complete objects *)

  Definition VB_ctor_spec : mpred :=
    □ Forall (this : ptr) (Q : ptr -> epred),
      this |-> tblockR (Tnamed "VB") 1$m **
      (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* this |-> VBR 1$m -* Q p)
      -* wp_fptr (type_of_value (Oconstructor
            (Build_Ctor "VB" nil CC_C Ar_Definite exception_spec.MayThrow None)))
           (_global "VB::VB()") [this] Q.

  Lemma G_complete_ok ρ (g : ptr) (Q : FreeTemps -> epred) :
    VB_ctor_spec **
    ctor_spec "G" "G::G()" (vbaseR "G" "VB" (VBR 1$m)) (GR 1$m) **
    (g |-> GR 1$m -* Q FreeTemps.id)
    |-- wp_init source ρ (Tnamed "G") g (Econstructor "G::G()" [] (Tnamed "G")) Q.
  Proof using Hσ.
    iIntros "(#SVB & #SG & HQ)".
    iApply wp_init_constructor; first done.
    erewrite glob_def_genv_compat_vstruct; last by vm_compute.
    rewrite /wp_init_complete_vstruct /ctor_fun_type /=.
    rewrite /wp_args /= /nd_seqs /= /wp.WPE.Mret.
    iIntros "!>" (pvbs Hlen) "F".
    destruct pvbs as [|pvb [|??]]; try done. cbn.
    repeat (case_bool_decide; try congruence).
    iDestruct "F" as "[[#V _] _]".
    rewrite wp_initialize_unqualified.unlock /=.
    (* 1. the virtual base, where the machine put it *)
    iApply wp_init_constructor; first done.
    erewrite glob_def_genv_compat_struct; last by vm_compute.
    rewrite /type_of_ctor /=.
    rewrite /wp_args /= /nd_seqs /= /wp.WPE.Mret.
    iIntros "!> BVB". iApply "SVB". iFrame "BVB".
    iIntros (p) "Hp VB".
    rewrite /= !interp_unfold /=. iModIntro. iFrame "Hp". iModIntro.
    (* 2. the constructor, on the non-virtual part *)
    iIntros "BG". iApply "SG". iFrame "BG".
    iSplitL "VB". { iApply (vbaseR_intro with "V VB"). }
    iIntros (p') "Hp' G". iModIntro. iFrame "Hp'". by iApply "HQ".
  Qed.

  Definition VB_dtor_spec : mpred :=
    □ Forall (this : ptr) (Q : ptr -> epred),
      this |-> VBR 1$m **
      (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
         this |-> tblockR (Tnamed "VB") 1$m -* Q p)
      -* wp_fptr (dtor_type "VB") (_global "VB::~VB()") [this] Q.

  (** Destroying a complete [G] also destroys its virtual base. *)
  Lemma G_destroy_ok (g : ptr) (Q : epred) :
    VB_dtor_spec **
    dtor_spec "G" "G::~G()" (GR 1$m) (vbaseR "G" "VB" (VBR 1$m)) **
    g |-> GR 1$m ** Q
    |-- wp_destroy_named source "G" g Q.
  Proof.
    iIntros "(#SVB & #SG & G & Q)".
    iApply wp_destroy_named_intro. cbn.
    rewrite /wp_destroy_vstruct /wp_base_destructor /wp_mfptr /=.
    iApply "SG". iFrame "G".
    iIntros (p) "Hp BG VB". iExists Vvoid. iFrame "Hp BG".
    iDestruct (_at_vbaseR with "VB") as (pvb) "[#V VB]".
    iExists pvb. iFrame "V".
    iApply wp_destructor_intro. rewrite /wp_mfptr /=.
    iApply "SVB". iFrame "VB".
    iIntros (p') "Hp' BVB". iExists Vvoid. iFrame.
  Qed.
End with_cpp.

(** ** What is not supported is stuck *)

cpp.prog stuck prog cpp:{{{
struct VB { int v; VB() {} };
// its constructor is only declared here
struct Decl : virtual VB { Decl(); };
// a virtual function in the hierarchy
struct PV { virtual void f() {} };
struct Poly : virtual PV { Poly() {} };
}}}.

(** The rules for constructors and destructors require a hierarchy
    without virtual functions. *)
Example poly_no : tu_no_vtables stuck "Poly" = false := eq_refl.
Example diamond_ok : tu_no_vtables source "G" = true := eq_refl.

(** Complete objects need a layout that [vstruct_layout_ok] accepts. *)
Definition layout_ok (tu : translation_unit) (cls : globname) : bool :=
  if tu.(types) !! cls is Some (Gvstruct vs) then vstruct_layout_ok tu cls vs else false.
Example diamond_layout_ok : layout_ok source "G" = true := eq_refl.

Section stuck.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** A complete object cannot be constructed with a constructor that is
      only declared: its initializers for the virtual bases are unknown. *)
  Lemma decl_stuck ρ vs (p : ptr) (Q : FreeTemps -> epred) :
    stuck.(types) !! "Decl"%cpp_name = Some (Gvstruct vs) ->
    wp_init_complete_vstruct stuck ρ "Decl" vs QM p "Decl::Decl()" [] Q |-- False.
  Proof.
    intros [= <-]. rewrite /wp_init_complete_vstruct /ctor_fun_type /=.
    apply UNSUPPORTED_elim.
  Qed.
End stuck.

(** ** Overlapping layouts

    The data of the pieces of a complete object (the virtual bases, then
    the non-virtual part) must be pairwise disjoint, but a piece may
    overlap the padding of another. The layouts below are clang's
    (x86-64). *)

cpp.prog overlap prog cpp:{{{
struct E {};
struct E2 {};
// [E] sits at offset 0, inside the non-virtual part.
struct Empty : virtual E { int x; Empty() {} };
// [E] and [E2] both sit at offset 0.
struct Two : virtual E, virtual E2 { int m; Two() {} };
struct V1 { long a; char c; V1() {} };
struct V2 { char d; };
// [V2] sits at offset 17, in the tail padding of [V1] (offsets 8 to 24).
struct Tail : virtual V1, virtual V2 { Tail() {} };
struct B { long a; char c; B() {} };
struct V { char v; };
// [V] sits at offset 18, in the tail padding of the base [B] (offsets 8
// to 24), whose storage is handed out after [V] is constructed: that
// storage does not cover [B]'s tail padding.
struct NvTail : B, virtual V { char g; NvTail() {} };
// [I] has no data but its vptr, which it shares with [Prim] at offset 0.
struct I { virtual ~I() {} };
struct Prim : virtual I { int x; Prim() {} };
struct X5 { char x; };
// The data of the non-virtual part of [W] is its vptr and [w]: offsets
// 0 to 9.
struct W : virtual X5 { char w; W() {} };
struct V3 { char d; };
// [W] at offset 8, [X5] at 17, [V3] at 18.
struct Outer : virtual W, virtual V3 { Outer() {} };
}}}.

Example empty_ok : layout_ok overlap "Empty" = true := eq_refl.
Example two_ok : layout_ok overlap "Two" = true := eq_refl.
Example tail_ok : layout_ok overlap "Tail" = true := eq_refl.
Example nv_tail_ok : layout_ok overlap "NvTail" = true := eq_refl.
Example prim_no : layout_ok overlap "Prim" = false := eq_refl.

(** Layout metadata is untrusted: a complete object whose alignment is
    not valid for its size is rejected (its [align_of] would be unknown,
    while its pieces claim alignment). *)
Example bad_alignment_no :
  if overlap.(types) !! "Empty"%cpp_name is Some (Gvstruct vs) then
    vstruct_layout_ok overlap "Empty"
      {| vs_struct := {| s_bases := vs.(vs_struct).(s_bases); s_fields := vs.(vs_struct).(s_fields);
                         s_virtuals := vs.(vs_struct).(s_virtuals); s_overrides := vs.(vs_struct).(s_overrides);
                         s_dtor := vs.(vs_struct).(s_dtor);
                         s_trivially_destructible := vs.(vs_struct).(s_trivially_destructible);
                         s_delete := vs.(vs_struct).(s_delete); s_layout := vs.(vs_struct).(s_layout);
                         s_size := vs.(vs_struct).(s_size); s_alignment := 0;
                         s_nonpublic_bases := vs.(vs_struct).(s_nonpublic_bases) |};
         vs_vbases := vs.(vs_vbases); vs_nv_alignment := vs.(vs_nv_alignment) |} = false
  else False := eq_refl.

Definition vs_with (vs : VStruct) (vbases : list (classname * LayoutInfo)) : VStruct :=
  {| vs_struct := vs.(vs_struct); vs_vbases := vbases;
     vs_nv_alignment := vs.(vs_nv_alignment) |}.

(** A virtual base without virtual bases needs room for its whole size,
    which its [type_ptr] covers once it is constructed, even when it has
    no data: [E] cannot sit at the end of [Empty]. *)
Example empty_at_end_no :
  match overlap.(types) !! "Empty"%cpp_name with
  | Some (Gvstruct e) =>
    vstruct_layout_ok overlap "Empty"
      (vs_with e [("E"%cpp_name, {| li_offset := 8 * Z.of_N e.(vs_struct).(s_size) |})]) = false
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** A piece may start right after the data of another, but not inside it:
    with [V3] moved from offset 18 to 17 ([X5] moving to 18), [V3] still
    avoids [W]'s data (offsets 8 to 17 of [Outer]); at offset 16 it would
    overlap [w]. *)
Example outer_data_boundary :
  match overlap.(types) !! "Outer"%cpp_name with
  | Some (Gvstruct o) =>
    let edit x5 v3 := vs_with o [("X5"%cpp_name, {| li_offset := x5 |});
                                 ("W"%cpp_name, {| li_offset := 64 |});
                                 ("V3"%cpp_name, {| li_offset := v3 |})] in
    [vstruct_layout_ok overlap "Outer" o;
     vstruct_layout_ok overlap "Outer" (edit 144 136);
     vstruct_layout_ok overlap "Outer" (edit 144 128)] = [true; true; false]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ** Misaligned bases

    The rules assume every pointer to a [C] is aligned to [alignof(C)],
    also at a base subobject, so every base must sit at an offset aligned
    to its class's full alignment. clang puts [C] at offset 8 in [D]
    below, while [alignof(C)] is 16 (see [doc/cpp/alignof.md]); cpp2v
    rejects [D], and so must the layout check, for a translation unit
    built by hand with clang's layout. *)

cpp.prog misaligned prog cpp:{{{
struct alignas(16) V { char v; };
struct C : virtual V { };
struct P : virtual V { };
struct D : P, C { };
}}}.

(** [D] with [C] at [c] bits, [V] at [v] bits, and [size] bytes. *)
Definition misaligned_D (c v : Z) (size : N) : VStruct := {|
  vs_struct := {|
    s_bases := [("P"%cpp_name, {| li_offset := 0 |}); ("C"%cpp_name, {| li_offset := c |})];
    s_fields := []; s_virtuals := []; s_overrides := [];
    s_dtor := "D::~D()"; s_trivially_destructible := true; s_delete := None;
    s_layout := Unspecified; s_size := size; s_alignment := 16;
    s_nonpublic_bases := [] |};
  vs_vbases := [("V"%cpp_name, {| li_offset := v |})];
  vs_nv_alignment := 8 |}.

Definition with_D (vs : VStruct) : translation_unit :=
  makeTranslationUnit misaligned.(symbols) (<["D"%cpp_name := Gvstruct vs]> misaligned.(types))
    misaligned.(namespace_aliases) misaligned.(initializer) misaligned.(asserts) misaligned.(abi)
    misaligned.(msymbols) misaligned.(mtypes) misaligned.(maliases) misaligned.(minstances)
    misaligned.(dropped_symbols).

(** clang's layout ([C] at 8, [V] at 16) is rejected; with [C] at 16
    ([V] at 32), the same hierarchy is accepted. *)
Example misaligned_base_no :
  let check c v size := vstruct_layout_ok (with_D (misaligned_D c v size)) "D" (misaligned_D c v size) in
  [check 64 128 32%N; check 128 256 48%N] = [false; true].
Proof. vm_compute. reflexivity. Qed.

Section overlap.
  Context `{Σ : cpp_logic} {σ : genv}.
  Hypothesis Hσ : overlap ⊧ σ.

  (** An empty virtual base sits at offset 0, inside the storage of the
      non-virtual part: a complete [Empty] can still be constructed and
      destroyed, because [E] has no data. *)
  Definition ER (q : cQp.t) : Rep := structR "E" q.
  Definition EmptyR (q : cQp.t) : Rep :=
    _field "Empty::x" |-> uninitR Tint q ** vbaseR "Empty" "E" (ER q).

  Definition E_ctor_spec : mpred :=
    □ Forall (this : ptr) (Q : ptr -> epred),
      this |-> tblockR (Tnamed "E") 1$m **
      (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* this |-> ER 1$m -* Q p)
      -* wp_fptr (type_of_value (Oconstructor
            (Build_Ctor "E" nil CC_C Ar_Definite exception_spec.NoThrow None)))
           (_global "E::E()") [this] Q.

  Lemma Empty_complete_ok ρ (e : ptr) (Q : FreeTemps -> epred) :
    E_ctor_spec **
    ctor_spec "Empty" "Empty::Empty()" (vbaseR "Empty" "E" (ER 1$m)) (EmptyR 1$m) **
    (e |-> EmptyR 1$m -* Q FreeTemps.id)
    |-- wp_init overlap ρ (Tnamed "Empty") e (Econstructor "Empty::Empty()" [] (Tnamed "Empty")) Q.
  Proof using Hσ.
    iIntros "(#SE & #SEm & HQ)".
    iApply wp_init_constructor; first done.
    erewrite glob_def_genv_compat_vstruct; last by vm_compute.
    rewrite /wp_init_complete_vstruct /ctor_fun_type /=.
    rewrite /wp_args /= /nd_seqs /= /wp.WPE.Mret.
    iIntros "!>" (pvbs Hlen) "F".
    destruct pvbs as [|pvb [|??]]; try done. cbn.
    repeat (case_bool_decide; try congruence).
    iDestruct "F" as "[[#V _] _]".
    rewrite wp_initialize_unqualified.unlock /=.
    (* 1. the empty virtual base, at the start of the object *)
    iApply wp_init_constructor; first done.
    erewrite glob_def_genv_compat_struct; last by vm_compute.
    rewrite /type_of_ctor /=.
    rewrite /wp_args /= /nd_seqs /= /wp.WPE.Mret.
    iIntros "!> BE". iApply "SE". iFrame "BE".
    iIntros (p) "Hp E".
    rewrite /= !interp_unfold /=. iModIntro. iFrame "Hp". iModIntro.
    (* 2. the constructor, on the non-virtual part, which overlaps [E] *)
    iIntros "BEm". iApply "SEm". iFrame "BEm".
    iSplitL "E". { iApply (vbaseR_intro with "V E"). }
    iIntros (p') "Hp' Em". iModIntro. iFrame "Hp'". by iApply "HQ".
  Qed.

  Definition E_dtor_spec : mpred :=
    □ Forall (this : ptr) (Q : ptr -> epred),
      this |-> ER 1$m **
      (Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
         this |-> tblockR (Tnamed "E") 1$m -* Q p)
      -* wp_fptr (dtor_type "E") (_global "E::~E()") [this] Q.

  Lemma Empty_destroy_ok (e : ptr) (Q : epred) :
    E_dtor_spec **
    dtor_spec "Empty" "Empty::~Empty()" (EmptyR 1$m) (vbaseR "Empty" "E" (ER 1$m)) **
    e |-> EmptyR 1$m ** Q
    |-- wp_destroy_named overlap "Empty" e Q.
  Proof.
    iIntros "(#SE & #SEm & Em & Q)".
    iApply wp_destroy_named_intro. cbn.
    rewrite /wp_destroy_vstruct /wp_base_destructor /wp_mfptr /=.
    iApply "SEm". iFrame "Em".
    iIntros (p) "Hp BEm E". iExists Vvoid. iFrame "Hp BEm".
    iDestruct (_at_vbaseR with "E") as (pvb) "[#V E]".
    iExists pvb. iFrame "V".
    iApply wp_destructor_intro. rewrite /wp_mfptr /=.
    iApply "SE". iFrame "E".
    iIntros (p') "Hp' BE". iExists Vvoid. iFrame.
  Qed.
End overlap.
