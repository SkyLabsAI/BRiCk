(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

let firsts = [|
{rocq|
Inductive N :=
  | O : N
  | S : N -> N.

(* Some comment. *)
|rocq};
{rocq|
Fixpoint add (n m : N) : N :=
  match n with
  | O => m
  | S n => S (add n m)
  end.
|rocq};
{rocq|
Lemma add_O_l (n : N) : add O n = n.
Proof.
  reflexivity.
Qed.
|rocq};
{rocq|
Lemma add_S_l (n m : N) : add (S n) m = S (add n m).
Proof.
  reflexivity.
Qed.
|rocq};
{rocq|
Lemma add_O_r (n : N) : add n O = n.
Proof.
  induction n as [|n IH].
  - rewrite add_O_l. reflexivity.
  - rewrite add_S_l. rewrite IH. reflexivity.
Qed.
|rocq};
{rocq|
Lemma add_S_r (n m : N) : add n (S m) = S (add n m).
Proof.
  induction n as [|n IH].
  - rewrite add_O_l. rewrite add_O_l. reflexivity.
  - rewrite add_S_l. rewrite add_S_l. rewrite IH. reflexivity.
Qed.
|rocq};
{rocq|
Lemma add_comm (n m : N) : add n m = add m n.
Proof.
  induction n as [|n IH].
  - rewrite add_O_l. rewrite add_O_r. reflexivity.
  - rewrite add_S_l. rewrite add_S_r. rewrite IH. reflexivity.
Qed.

(* Some comment. *)
|rocq};
|]

let extra =
{rocq|
Goal forall (n m : N), add n m = add m n.
Proof.
  intro n. intro m.
  induction n as [|n IH].
  - rewrite add_O_l. rewrite add_O_r. reflexivity.
  - rewrite add_S_l. rewrite add_S_r. rewrite IH. reflexivity.
Qed.

(* Some comment. *)
|rocq}

let _ =
  let n = try int_of_string Sys.argv.(1) with Failure _ -> assert false in
  assert (n >= 0);
  Printf.fprintf stdout "(* Generated file, do not edit. *)\n";
  for i = 1 to min n (Array.length firsts) do
    output_string stdout firsts.(i-1)
  done;
  for _ = 1 to n - Array.length firsts do
    output_string stdout extra
  done;
  Printf.fprintf stdout "%!"
