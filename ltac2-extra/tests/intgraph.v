(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Ltac2.Ltac2.
Require Import skylabs.ltac2.extra.internal.list.
Require Import skylabs.ltac2.extra.internal.control.
Require Import skylabs.ltac2.extra.internal.intgraph.

Module Tests.
  Import IntGraph.

  Ltac2 eq ls1 ls2 :=
    (List.for_all2 (fun (a,b) (x,y) => Bool.and (Int.equal a x) (Int.equal b y))) ls1 ls2.
  Goal True.
    let g1 := of_edges [(1,3); (15,1); (-2,-3)] in
    let g2 := of_edges [(15,1); (-2,-3); (1,3)] in
    if equal g1 g2 then () else throw_invalid! "test failure".

    let g := of_edges [(1,3); (15,1); (-2,-3)] in
    if path (1,3) g then () else throw_invalid! "test failure".

    let ls := sublists -100 100  (List.sort cmp [(1,3); (-2,15); (15,1); (-2,-3)]) in
    if List.for_all2 eq ls [[(-2, 15); (-2, -3)]; [(1, 3)]; [(15, 1)]] then ()
    else throw_invalid! "test failure".

    let tr := trans_clos (of_edges [(1,3); (-2,15); (15,1); (-2,-3)]) in
    let _ :=
      if eq (tr.(edges)) [(-2, -3); (-2, 1); (-2, 3); (-2, 15); (1, 3); (15, 1); (15, 3)] then ()
      else throw_invalid! "test failure"
    in
    if eq (tr.(redges)) [(-3, -2); (1, -2); (1, 15); (3, -2); (3, 1); (3, 15); (15, -2)] then ()
    else throw_invalid! "test failure".


    let r := roots (trans_clos (of_edges [(1,3); (-2,15); (15,1); (-2,-3)])) in
    if List.for_all2 Int.equal r [-2] then () else throw_invalid! "test failure".

    let es := edges_from -2 (trans_clos (of_edges [(1,3); (-2,15); (15,1); (-2,-3)])) in
    if eq es [(-2, 15); (-2, 3); (-2, 1); (-2, -3)] then ()
    else throw_invalid! "test failure".

    let os := in_order (trans_clos (of_edges [(1,3); (-2,15); (15,1); (-2,-3)])) in
    if List.for_all2 Int.equal os [-2; -3; 15; 1; 3] then ()
    else throw_invalid! "test failure".

    let ls := leaves ((of_edges [(1,3); (-2,15); (15,1); (-2,-3)])) in
    if List.for_all2 Int.equal ls [-3;3] then ()
    else throw_invalid! "test failure".

    let ls := leaves (trans_clos (of_edges [(1,3); (-2,15); (15,1); (-2,-3)])) in
    if List.for_all2 Int.equal ls [-3;3] then ()
    else throw_invalid! "test failure".

    let os := in_rev_order (trans_clos (of_edges [(1,3); (-2,15); (15,1); (-2,-3)])) in
    if List.for_all2 Int.equal os [-3; 3; 1; 15; -2] then ()
    else throw_invalid! "test failure".

    let g1 := of_edges [(1,3); (15,1); (-2,-3)] in
    let g2 := add (15,1) (of_edges [(1,3); (15,1); (-2,-3)]) in
    if equal g1 g2 then () else throw_invalid! "test failure".

    let g1 := of_edges [(1,3); (15,1); (-2,-3)] in
    let g2 := of_edges [(15,1); (3,1)] in
    let w := without g1 g2 in
    if eq (w.(edges)) [(-2, -3); (1, 3)] then ()
    else throw_invalid! "test failure".

    exact I.
  Qed.
End Tests.


