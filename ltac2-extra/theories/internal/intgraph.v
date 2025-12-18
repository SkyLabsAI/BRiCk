(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Ltac2.Ltac2.
Require Import skylabs.ltac2.extra.internal.list.
Require Import skylabs.ltac2.extra.internal.control.


(** Naive representation of sparse graphs with integer nodes. *)
Module IntGraph.
  Ltac2 Type t := {
    (* Edges (sorted). *)
    edges : (int * int) list;
    (* Reverse edges (sorted). *)
    redges : (int * int) list;
    (* Smaller than smallest node. *)
    inf : int;
    (* Bigger than largest node. *)
    sup : int;
  }.

  Ltac2 cmp (a,b) (x,y) :=
    let c := Int.compare a x in
    if Int.equal c 0 then Int.compare b y else c.

  Ltac2 find (ab : _ * _) : _ list -> bool * _ list * _ list :=
    let rec go acc l :=
      match l with
      | [] => false, acc, l
      | xy :: l =>
        let c := cmp ab xy in
        if Int.lt c 0 then
          false, acc, (xy :: l)
        else
        if Int.gt c 0 then
          go (xy :: acc) l
        else
          true, acc, l
      end
    in go [].

  (* returns [true] if the list has changed *)
  Ltac2 add_edge edge edges : bool * _ list :=
    match find edge edges with
    | true, _, _ => false, edges
    | false, before, after => true, List.rev_append before (edge :: after)
    end.

  Ltac2 add_edges edges1 edges2 : bool * _ list :=
    List.foldl (fun edge (changed, edges) =>
                    let (changed', edges) := add_edge edge edges in
                    (Bool.or changed changed', edges)
      ) edges1 (false, edges2).

  Ltac2 inv_edge (a,b) := (b,a).
  Ltac2 max a b := if Int.ge a b then a else b.
  Ltac2 maxs xs := List.fold_left max 0 xs.
  Ltac2 min a b := if Int.le a b then a else b.
  Ltac2 mins xs := List.fold_left min 0 xs.

  Ltac2 add edge (t : t) : t :=
    let (changed, edges) := add_edge edge (t.(edges)) in
    if Bool.neg changed then t
    else
      let (from,to) := edge in
      let (_, redges) := add_edge (to,from) (t.(redges)) in
      let inf := min (t.(inf)) (Int.sub (min from to) 1) in
      let sup := max (t.(sup)) (Int.add (max from to) 1) in
      { edges := edges; redges := redges; sup := sup; inf := inf }.


  (* returns [true] if the list has changed *)
  Ltac2 del_edge edge edges : bool * _ list :=
    match find edge edges with
    | false, _, _ => false, edges
    | true, before, after => true, List.rev_append before (after)
    end.

  Ltac2 del edge (t : t) : t :=
    let (changed, edges) := del_edge edge (t.(edges)) in
    if Bool.neg changed then t
    else
      let (from,to) := edge in
      let (_, redges) := del_edge (to,from) (t.(redges)) in
      { edges := edges; redges := redges; sup := t.(sup); inf := t.(inf) }.

  Ltac2 sublist a inf sup ls : _ list * _ list * _ list :=
    (* left border of sublist of interest *)
    match find (a, inf) ls with
    | true, _, _ =>
        throw_invalid! "invariant violated: (_, t.(inf)) exists in list"
    | false, before, after =>
        (* right border of sublist of interest *)
        match find (a, sup) after with
        | true, _, _ =>
            throw_invalid! "invariant violated: (_, t.(sup)) exists in list"
        | false, es, after => before, es, after
        end
    end.


  Ltac2 edges_from' a inf sup edges : (_ * _) list :=
    let (_ , xs, _) := sublist a inf sup edges in xs.
  (** [edges_from a t] returns all edges from [a] to any other node [b] in
      reverse order on [b] *)
  Ltac2 edges_from a t : (_ * _) list :=
    edges_from' a (t.(inf)) (t.(sup)) (t.(edges)).

  Ltac2 edges_to' b inf sup edges : (_ * _) list :=
    let (_, xs, _) := sublist b inf sup edges in List.map inv_edge xs.
  (** [edges_to b t] returns all edges to [b] from any other node [a] in
      reverse order on [a] *)
  Ltac2 edges_to b t : (_ * _) list :=
    edges_to' b (t.(inf)) (t.(sup)) (t.(redges)).


  (** [add_trans (x,y) t] adds edge [(x,y)] and edges [(x,z)] for all [(y,z)]
      in [t]. [add_trans (x,y) t] is transitively closed if [t] is. *)
  Ltac2 add_trans (x,y) (t : t) : t :=
    let edges := (x,y) :: List.map (fun (_, z) => (x,z)) (edges_from y t) in
    List.foldl add edges t.

  Ltac2 mem edge t : bool :=
    let (res, _, _) := find edge (t.(edges)) in
    res.
  Ltac2 has t edge := mem edge t.

  Ltac2 has_from from t : bool :=
    let (_, _, after) := find (from, t.(inf)) (t.(edges)) in
    Option.default false (Option.map (fun (from', _) =>
      Int.equal from from') (List.hd_opt after)).

  Ltac2 has_to to (t : t) : bool :=
    let (_, _, after) := find (to, t.(inf)) (t.(redges)) in
    Option.default false (Option.map (fun (_, to') =>
      Int.equal to to') (List.hd_opt after)).

  Ltac2 path (from,to) (t : t) : bool :=
    if Bool.or (Int.le from (t.(inf))) (Int.le to (t.(inf))) then false else
    if Bool.or (Int.ge to (t.(sup))) (Int.ge from (t.(sup))) then false else
    let off := Int.add (t.(inf)) 1 in
    let length := Int.sub (t.(sup)) off in
    let froms := Array.make length false in
    Array.set froms (Int.sub from off) true;
    let tos := Array.make length false in
    Array.set tos (Int.sub to off) true;
    let progress := Ref.ref true in
    let done := Ref.ref false in
    let update arr i :=
      match Array.get arr (Int.sub i off) with
      | true => ()
      | false => Array.set arr (Int.sub i off) true; Ref.set progress true
      end
    in
    let rec go () :=
      Array.iteri (fun i from =>
                     let to := Array.get tos i in
                     if Bool.and from to then Ref.set done true else ()
        ) froms;
      match Ref.get done with
      | true => true
      | false =>
        Ref.set progress false;
        Array.iteri (
            fun from b =>
              if b then
                List.iter (fun (_, from') =>
                  update froms from') (edges_from (Int.add from off) t)
              else ()
          ) froms;
        Array.iteri (
            fun to b =>
              if b then
                List.iter (fun (to', _) =>
                  update tos to') (edges_to (Int.add to off) t)
              else ()
          ) tos;
        match Ref.get progress with
        | false => false
        | true => go ()
        end
      end
    in go ().

  Ltac2 of_edges (edges : (_ * _) list) : t :=
    let edges := List.sort cmp edges in
    let redges := List.sort cmp (List.map inv_edge edges) in
    let (inf, sup) :=
      List.foldl (fun (from,to) (inf, sup) =>
                    let inf := mins [Int.sub from 1; Int.sub to 1; inf] in
                    let sup := maxs [Int.add from 1; Int.add to 1; sup] in
                    (inf, sup)
        ) edges (0,0)
    in
    { edges := edges; redges := redges; inf := inf; sup := sup }.

  Ltac2 nodes' edges :=
    let fst (x,_) := x in let snd (_,y) := y in
    List.sort_uniq Int.compare
      (List.rev_append (List.map fst edges) (List.map snd edges)).

  Ltac2 nodes (t : t) : _ list := nodes' (t.(edges)).

  (** [without t1 t2] only keeps exactly those edges of [t1] that do not exist
      in [t2]. *)
  Ltac2 without (t1 : t) (t2 : t) : t :=
    let rec filter acc t2_edges t1_edges :=
      match t1_edges with
      | [] => List.rev acc
      | ab :: t1_edges =>
        let (found, _, t2_edges) := find ab t2_edges in
        if found then
          filter acc t2_edges t1_edges
        else
          filter (ab :: acc) t2_edges t1_edges
      end
    in
    let edges := filter [] (t2.(edges)) (t1.(edges)) in
    of_edges edges.

  Ltac2 equal (t1 : t) (t2 : t) :=
    List.for_all2 (fun (a,b) (x,y) =>
      Bool.and (Int.equal a x) (Int.equal b y)) (t1.(edges)) (t2.(edges)).

  Ltac2 rec sublists inf sup edges :=
    match edges with
    | [] => []
    | (x, _) :: _ =>
        let (_, xs, edges) := sublist x inf sup edges in
        xs :: sublists inf sup edges
    end.


  Ltac2 roots (t : t) : _ list :=
    List.map_filter (fun x =>
      match edges_to x t with [] => Some x | _ => None end) (nodes t).

  Ltac2 leaves (t : t) : _ list :=
    List.map_filter (fun x =>
      match edges_from x t with [] => Some x | _ => None end) (nodes t).

  Ltac2 inv (t : t) :=
    { t with edges := t.(redges); redges := t.(edges) }.

  Ltac2 trans_clos (t : t) :=
    let rec clos f edges :=
      let (changed, edges) :=
        List.foldl (
          List.foldl (fun (x,y) (changed, edges) =>
            let new_edges := f x y edges in
            let (changed', edges) := add_edges new_edges edges in
            (Bool.or changed changed', edges)
          )
        ) (sublists (t.(inf)) (t.(sup)) edges) (false, edges)
      in
      if changed then clos f edges else edges
    in
    let edges :=
      clos (fun x y edges =>
        List.map (fun (_, z) =>
          (x,z)) (edges_from' y (t.(inf)) (t.(sup)) edges)
        ) (t.(edges))
    in
    (* TODO: [redges] doesn't work. We recompute from [edges] *)
    (* let redges := *)
    (*   clos (fun y x redges => *)
    (*     List.map (fun (_,z) => *)
    (*       (z,x)) (edges_to' y (t.(inf)) (t.(sup)) redges) *)
    (*     ) (t.(redges)) *)
    (* in *)
    let redges := List.sort_uniq cmp (List.map (fun (x,y) => (y,x)) edges) in
    { edges := edges; redges := redges; inf := t.(inf); sup := t.(sup) }.


  Ltac2 in_order (t : t) :=
    (* [https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm] *)
    let l : int list := [] in
    let s : int list := roots t in
    let rec loop (t : t) (l : int list) (s : int list) :=
      match s with
      | [] => (t, l)
      | n :: s =>
        let l := n :: l in
        let (t, s) :=
          List.foldl (fun (_, m) (t,s) =>
            let e := (n, m) in
            let t := del e t in
            let s := match edges_to m t with [] => m :: s | _ => s end in
            (t, s)
          ) (edges_from n t) (t, s)
        in
        loop t l s
      end
    in
    let (t,l) := loop t l s in
    match t.(edges) with
    | [] => List.rev l
    | _ => throw_invalid! "cycle detected"
    end
  .

  Ltac2 in_rev_order (t : t) := in_order (inv t).

  Ltac2 Type exn ::= [ Graph (t) ].
  Ltac2 msg (t : t) :=
    Message.of_exn (Graph t).
End IntGraph.
