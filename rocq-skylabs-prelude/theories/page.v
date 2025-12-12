(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.addr.
Require Import bluerock.prelude.numbers.

(** 4KB pages are addressed by 12 bits *)
Definition PAGE_BITS : N  := 12.
Definition PAGE_SIZE : N := 2 ^ 12.

Theorem PAGE_bits_size : PAGE_SIZE = (2 ^ PAGE_BITS)%N.
Proof. reflexivity. Qed.

Definition page_align_dn (addr : N) : N := Z.to_N $ align_dn addr PAGE_BITS.
Lemma page_align_dn_below addr : (page_align_dn addr <= addr)%N.
Proof.
  have ?: (align_dn addr PAGE_BITS <= addr)%Z.
  { exact: align_dn_below. }
  rewrite /page_align_dn; lia.
Qed.

Lemma page_align_dn_mod addr :
  (page_align_dn addr mod PAGE_SIZE = 0)%N.
Proof.
  rewrite -(N2Z.id PAGE_SIZE) /page_align_dn PAGE_bits_size.
  apply N.Lcm0.mod_divide, Z2N_inj_divide, align_dn_divide; try lia.
  apply /align_dn_nonneg; lia.
Qed.

Definition page_align_up (addr : N) := Z.to_N $ align_up addr PAGE_BITS.
#[global] Notation page_aligned addr :=
    (N.eqb 0 (addr mod PAGE_SIZE)) (only parsing).

Lemma page_align_up_mod addr :
  (page_align_up addr mod PAGE_SIZE = 0)%N.
Proof.
  rewrite -(N2Z.id PAGE_SIZE) /page_align_up PAGE_bits_size.
  apply N.Lcm0.mod_divide, Z2N_inj_divide, align_up_divide; try lia.
  apply /align_up_nonneg; lia.
Qed.

Lemma page_align_up_below addr : (addr <= page_align_up addr)%N.
Proof.
  have ?: (addr <= numbers.align_up addr PAGE_BITS)%Z.
  { exact: numbers.align_up_below. }
  rewrite /page_align_up; lia.
Qed.

Definition page_offset_of (addr : N) := (addr - page_align_dn addr)%N.
Definition qPAGE_SIZE : Qp := N_to_Qp PAGE_SIZE.

Lemma page_align_dn_offset_of addr :
  addr = (page_align_dn addr + page_offset_of addr)%N.
Proof.
  rewrite /page_offset_of comm_L N.sub_add //.
  exact: page_align_dn_below.
Qed.

Lemma page_align_ofs_eq a1 a2 :
  page_align_dn a1 = page_align_dn a2 ->
  page_offset_of a1 = page_offset_of a2 ->
  a1 = a2.
Proof.
  intros h1 h2.
  by rewrite (page_align_dn_offset_of a1) (page_align_dn_offset_of a2) h1 h2.
Qed.

Definition page_offset (va : vaddr) : vaddr * N :=
  (page_align_dn va, page_offset_of va).

(** Page attributes *)
Module attrs.
(**
TODO FM-1051: Strictly speaking, this belongs to the NOVA specs, since this is
NOVA's abstraction of page mapping attributes, and need not have a canonical
mapping to hardware page attributes.
*)
Record t : Set :=
{ read  : bool
; write : bool
; uexec : bool
; sexec : bool }.
(** Page Table Entry *)
Definition pteT : Set := paddr * attrs.t.
(** Optional Page Table Entry *)
Definition opteT : Set := option pteT.

#[deprecated(note="")]
Notation user := uexec (only parsing).

Definition none : t :=
{| read := false ; write := false ; sexec := false ; uexec := false |}.

Definition R : t :=
{| read := true ; write := false ; sexec := false ; uexec := false |}.

Definition W : t :=
{| read := false ; write := true ; sexec := false ; uexec := false |}.

Definition RW : t :=
{| read := true ; write := true ; sexec := false ; uexec := false |}.

Definition RWX : t :=
{| read := true ; write := true ; sexec := true ; uexec := true |}.

#[global] Instance t_eq_dec : EqDecision t.
Proof. solve_decision. Defined.

#[global] Instance t_inhabited : Inhabited t := populate R.

#[global] Instance t_countable : Countable t.
Proof.
  apply (inj_countable'
    (λ a : t, ((read a, write a), (uexec a, sexec a)))
    (λ n, {| read := n.1.1 ; write := n.1.2 ; uexec := n.2.1 ; sexec := n.2.2 |})).
  abstract (by intros []).
Qed.

Definition is_r (a : attrs.t) : bool :=
  a.(read).

Definition is_rw (a : attrs.t) : bool :=
  a.(read) && a.(write).

Definition is_rwux (a : attrs.t) : bool :=
  is_rw a && a.(uexec).

Definition is_rwsx (a : attrs.t) : bool :=
  is_rw a && a.(sexec).

Definition nonnull (a : attrs.t) : bool :=
  read a || write a || uexec a || sexec a.

Definition masked (perm_mask : N) (a : attrs.t) : attrs.t :=
  {| read  := andb (N.testbit perm_mask 0) (read  a)
   ; write := andb (N.testbit perm_mask 1) (write a)
   ; uexec := andb (N.testbit perm_mask 2) (uexec a)
   ; sexec := andb (N.testbit perm_mask 3) (sexec a)
  |}.

Definition masked_opt (perm_mask : N) (a : attrs.t) : option attrs.t :=
  let res := masked perm_mask a in
  guard (nonnull res);; Some res.

Definition opte_mask (perm_mask : N) (opte : opteT) : opteT :=
  '(pa, pte) ← opte;
  masked ← masked_opt perm_mask pte;
  Some (pa, masked).

End attrs.
Notation pteT := attrs.pteT.
Notation opteT := attrs.opteT.

(** page table levels, 0 is the smallest page table level *)
Definition Level : Set := nat.
Bind Scope nat_scope with Level.
