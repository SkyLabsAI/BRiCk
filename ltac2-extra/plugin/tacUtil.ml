(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Stdlib_extra.Extra
open Ltac2_plugin
module Decl = Context.Rel.Declaration

type 'a tactic = 'a Proofview.tactic

(* helper for functions that work on 0, 1, or many goals. *)
let with_evarmap f =
  let open Proofview.Notations in
  Proofview.numgoals >>= fun numgoals ->
  if numgoals == 1 then
    Proofview.Goal.enter_one (fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        f sigma
      )
  else Proofview.tclEVARMAP >>= f

let evar_map : Evd.evar_map Proofview.tactic =
  with_evarmap Proofview.tclUNIT

let env : Environ.env Proofview.tactic =
  let open Proofview.Notations in
  Proofview.numgoals >>= fun numgoals ->
  if numgoals == 1 then
    Proofview.Goal.enter_one @@ fun gl ->
    Proofview.tclUNIT (Proofview.Goal.env gl)
  else Proofview.tclENV

module Notations = struct
  let return = Proofview.tclUNIT
  let (>>=) = Proofview.tclBIND
  let (<*>) = Proofview.tclTHEN
end

module Value = struct
  open Notations

  include Tac2ffi
  include Tac2val

  let thaw1_poly (f : valexpr) : valexpr tactic -> valexpr tactic =
    let f = Tac2ffi.to_closure f in
    fun v -> v >>= fun v -> Tac2val.apply f [v]

  let thaw1 (type a b) (ra : a repr) (rb : b repr) (f : valexpr) : a -> b tactic =
    Tac2ffi.to_fun1 (repr_of ra) (repr_to rb) f

  let thaw2 (type a b c) (ra : a repr) (rb : b repr) (rc : c repr) (f : valexpr) :
      a -> b -> c tactic =
    let f = thaw1 ra (Tac2ffi.fun1 rb rc) f in
    fun a b ->
    f a >>= fun f ->
    f b

  let thaw3 (type a b c d) (ra : a repr) (rb : b repr) (rc : c repr) (rd : d repr)
      (f : valexpr) : a -> b -> c -> d tactic =
    let f = thaw2 ra rb (Tac2ffi.fun1 rc rd) f in
    fun a b c ->
    f a b >>= fun f ->
    f c

  type binder = Names.Name.t EConstr.binder_annot * EConstr.types

  (** Must agree with Ltac2 type [Constr.Unsafe.RelDecl.t] *)
  let of_rel_declaration (decl : EConstr.rel_declaration) : valexpr =
    match decl with
    | Decl.LocalAssum (a,t) -> of_fat @@ ValBlk (0, [|of_binder (a,t)|])
    | Decl.LocalDef (a,c,t) -> of_fat @@ ValBlk (1, [|of_binder (a,t); of_constr c|])

  (** Must agree with Ltac2 type [Constr.Unsafe.RelDecl.t] *)
  let to_rel_declaration (v : valexpr) : EConstr.rel_declaration =
    match unsafe_to_fat v with
    | ValBlk (0, [|b|]) -> let a,t = to_binder b in Decl.LocalAssum (a,t)
    | ValBlk (1, [|b;c|]) ->
      let a,t = to_binder b in Decl.LocalDef (a,to_constr c,t)
    | _ -> assert false

  let rel_declaration : EConstr.rel_declaration repr =
    make_repr of_rel_declaration to_rel_declaration

  module RawConstr =
  struct
    let to_constr (sigma : Evd.evar_map) (c : valexpr) : Constr.t =
      EConstr.to_constr ~abort_on_undefined_evars:false sigma (to_constr c)

    let of_constr (c : Constr.t) : valexpr =
      of_constr (EConstr.of_constr c)
  end

end

let timed : 'a Proofview.tactic -> (float * 'a) Proofview.tactic = fun f ->
  let open Proofview.Notations in
  Proofview.tclUNIT () >>= fun _ ->
  let t0 = Time.Unix.get () in
  f >>= fun v ->
  let t1 = Time.Unix.get () in
  Proofview.tclUNIT (t1 -. t0, v)


