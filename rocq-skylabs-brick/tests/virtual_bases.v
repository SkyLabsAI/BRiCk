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
  Definition LR (q : cQp.t) : Rep := vbaseR "L" "VB" (VBR q).
  Definition RR (q : cQp.t) : Rep := vbaseR "R" "VB" (VBR q).
  Definition G_pre (q : cQp.t) : Rep := _field "G::g" |-> uninitR Tint q.
  Definition GR (q : cQp.t) : Rep := G_pre q ** vbaseR "G" "VB" (VBR q).

  (** A full [Rep] is fractional, although it hides where the virtual
      base is. *)
  #[local] Instance VBR_cfractional : CFractional VBR.
  Proof. rewrite /VBR. apply _. Qed.
  #[local] Instance GR_cfractional : CFractional GR.
  Proof. rewrite /GR /G_pre. apply _. Qed.

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
    iIntros (p) "Hp L".
    rewrite /= !interp_unfold /=. iModIntro. iFrame "Hp". iModIntro.
    (* Take the virtual base back, and lend it to [R]. *)
    iDestruct (vbaseR_elim with "VL L") as "VB".
    iExists pvb. iFrame "V". iIntros "#VR !> BR". iApply "SR". iFrame "BR".
    iSplitL "VB". { iApply (vbaseR_intro with "VR VB"). }
    iIntros (p') "Hp' R".
    iModIntro. iFrame "Hp'". iModIntro.
    iDestruct (vbaseR_elim with "VR R") as "VB".
    (* the field of [G] *)
    default_initialize_unfold. cbn.
    iIntros "Hg !>". rewrite interp_unfold /=. iModIntro.
    (* the body *)
    iApply wp_seq. rewrite wp_block_unfold. iIntros "!> !> !>". cbn.
    iIntros "!> %p0 Hp0". iApply ("HQ" with "Hp0").
    rewrite /GR /G_pre _at_sep _at_offsetR. iFrame "Hg".
    iApply (vbaseR_intro with "V VB").
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
    rewrite /GR /G_pre _at_sep _at_offsetR. iDestruct "G" as "[Hg VB]".
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
    iApply "SR". iSplitL "VB". { iApply (vbaseR_intro with "VR VB"). }
    iIntros (p) "Hp BR VB". iExists Vvoid. iFrame "Hp BR".
    iDestruct (vbaseR_elim with "VR VB") as "VB".
    iExists pvb. iFrame "V". iIntros "#VL".
    iApply "SL". iSplitL "VB". { iApply (vbaseR_intro with "VL VB"). }
    iIntros (p') "Hp' BL VB". iExists Vvoid. iFrame "Hp' BL".
    iDestruct (vbaseR_elim with "VL VB") as "VB".
    iIntros "BG !> %p0 Hp0". iApply ("HQ" with "Hp0 BG").
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
// an empty virtual base shares its address with the non-virtual part
struct E {};
struct Empty : virtual E { Empty() {} };
}}}.

(** The rules for constructors and destructors require a hierarchy
    without virtual functions. *)
Example poly_no : tu_no_vtables stuck "Poly" = false := eq_refl.
Example diamond_ok : tu_no_vtables source "G" = true := eq_refl.

(** Complete objects need a layout in which the virtual bases do not
    overlap anything. *)
Definition layout_ok (tu : translation_unit) (cls : globname) : bool :=
  if tu.(types) !! cls is Some (Gvstruct vs) then vstruct_layout_ok tu vs else false.
Example empty_no : layout_ok stuck "Empty" = false := eq_refl.
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
