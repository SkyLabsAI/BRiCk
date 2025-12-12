(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.coPset stdpp.telescopes.
Require Import iris.bi.lib.atomic.
Require Import bluerock.iris.extra.bi.atomic_commit.
Require Import bluerock.iris.extra.bi.atomic1.

(** Notation for atomic reads. *)

Notation "'AR' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' Φ '>>'" :=
  (*
  We want
  [(AC << ∃ x1 .. xn , α >> @ Eo , Ei << α%I, COMM Φ >>)%I]
  but that's rejected, so:
  *)
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 false
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) α%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, Φ at level 200, x1 binder, xn binder) : bi_scope.

Notation "'AR1' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' Φ '>>'" :=
  (* [(AC1 << ∃ x1 .. xn , α >> @ Eo , Ei << α%I, COMM Φ >>)%I] *)
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 true
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) α%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, Φ at level 200, x1 binder, xn binder) : bi_scope.

(** Reusable atomic read. *)
Notation "'AR+' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' Φ '>>'" :=
  (* [(AU << ∃ x1 .. xn , α >> @ Eo , Ei << α%I, COMM Φ >>)%I] *)
  (atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) α%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, Φ at level 200, x1 binder, xn binder) : bi_scope.

(** Reusable atomic read, >= 1-step. *)
Notation "'AR1+' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' Φ '>>'" :=
  (* [(AU1 << ∃ x1 .. xn , α >> @ Eo , Ei << α%I, COMM Φ >>)%I] *)
  (atomic1_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) α%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, Φ at level 200, x1 binder, xn binder) : bi_scope.
