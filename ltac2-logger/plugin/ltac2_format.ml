(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin

type msg_item =
  | String of string
  | Int    of int
  | Constr of Environ.env * Evd.evar_map * EConstr.t
  | Ast    of EConstr.t
  | Ident  of Names.Id.t
  | Msg    of msg_item list
  | Thunk  of (unit -> msg_item)
  | Pp     of Pp.t

type msg = msg_item list

let msg_tag : msg Tac2dyn.Val.tag = Tac2dyn.Val.create "msg"
let msg_repr = Tac2ffi.repr_ext msg_tag

let unit_valexpr : Tac2val.valexpr = Tac2ffi.of_unit ()

let build_msg : Environ.env -> Evd.evar_map -> Tac2types.format list ->
    Tac2val.valexpr list -> msg = fun env sigma fs args ->
  let rec build acc fs args =
    let open Tac2types in
    let _String s = String(Tac2ffi.to_string s) in
    let _Int i = Int(Tac2ffi.to_int i) in
    let _Constr c = Constr(env, sigma, Tac2ffi.to_constr c) in
    let _Ident i = Ident(Tac2ffi.to_ident i) in
    let _Pp p = Pp(Tac2ffi.to_pp p) in
    let _Msg m = Msg(Tac2ffi.to_ext msg_tag m) in
    let _Thunk f x =
      let thunk () =
        let tac =
          let open Proofview.Notations in
          Tac2val.apply (Tac2ffi.to_closure f) [unit_valexpr; x] >>= fun m ->
          Proofview.tclUNIT (_Msg m)
        in
        let name = Names.Id.of_string "XXX" in
        let (_, pv) = Proofview.init sigma [] in
        let (r,_, _, _, _) = Proofview.apply ~name ~poly:false env tac pv in
        r
      in
      Thunk(thunk)
    in
    let _Thunk0 f x =
      let thunk () =
        let tac =
          let open Proofview.Notations in
          Tac2val.apply (Tac2ffi.to_closure f) [x] >>= fun m ->
          Proofview.tclUNIT (_Msg m)
        in
        let name = Names.Id.of_string "XXX" in
        let (_, pv) = Proofview.init sigma [] in
        let (r,_, _, _, _) = Proofview.apply ~name ~poly:false env tac pv in
        r
      in
      Thunk(thunk)
    in
    match (fs, args) with
    | ([]                 , []            ) ->
        List.rev acc
    | (FmtLiteral(s) :: fs, _             ) ->
        build (String(s)  :: acc) fs args
    | (FmtString     :: fs, s      :: args) ->
        build (_String s  :: acc) fs args
    | (FmtInt        :: fs, i      :: args) ->
        build (_Int i     :: acc) fs args
    | (FmtConstr     :: fs, c      :: args) ->
        build (_Constr c  :: acc) fs args
    | (FmtIdent      :: fs, i      :: args) ->
        build (_Ident i   :: acc) fs args
    | (FmtAlpha      :: fs, f :: x :: args) ->
        build (_Thunk f x :: acc) fs args
    | (FmtAlpha0     :: fs, f :: x :: args) ->
        build (_Thunk0 f x :: acc) fs args
    | (FmtMessage    :: fs, p      :: args) ->
        build (_Pp p :: acc) fs args
    | (_                  , _             ) -> assert false
  in
  build [] fs args

(* TODO: figure out if we can share this code with [misc.ml] later. *)
let with_env_and_sigma tac =
  let open Proofview.Notations in
  Proofview.Goal.goals >>= fun gs ->
  match gs with
  | []  ->
      Proofview.tclENV >>= fun env ->
      Proofview.tclEVARMAP >>= fun sigma ->
      Proofview.tclUNIT (tac env sigma)
  | [g] ->
      g >>= fun g ->
      let env = Proofview.Goal.env g in
      let sigma = Proofview.Goal.sigma g in
      Proofview.tclUNIT (tac env sigma)
  | _   ->
      (* It doesn't make much sense to compose printing functions with tactics
         that produce several goals, so we forbid this. *)
      assert false (* FIXME better error. *)

let build_msg : Tac2types.format list -> Tac2val.valexpr list ->
    msg Proofview.tactic = fun fs args ->
  with_env_and_sigma (fun env sigma -> build_msg env sigma fs args)

let arity : Tac2types.format list -> int =
  let open Tac2types in
  let fn acc tag =
    match tag with
    | FmtLiteral(_) -> acc
    | FmtString
    | FmtInt
    | FmtConstr
    | FmtMessage
    | FmtIdent      -> acc + 1
    | FmtAlpha      -> acc + 2
    | FmtAlpha0     -> acc + 2
  in
  List.fold_left fn 0

let ret_unit = Proofview.tclUNIT (Tac2ffi.of_unit ())

let eval : enabled:bool -> (msg -> unit) -> Tac2types.format list ->
    Tac2val.valexpr Proofview.tactic = fun ~enabled print fs ->
  let open Proofview.Notations in
  let eval =
    if enabled then
      (fun args -> build_msg fs args >>= fun msg -> print msg; ret_unit)
    else
      (fun _ -> ret_unit)
  in
  match arity fs with
  | 0 -> eval []
  | n -> Proofview.tclUNIT (Tac2ffi.of_closure (Tac2val.abstract n eval))

let eval_msg : Tac2types.format list -> Tac2val.valexpr Proofview.tactic =
    fun fs ->
  let open Proofview.Notations in
  let eval args =
    build_msg fs args >>= fun msg ->
    Proofview.tclUNIT (Tac2ffi.of_ext msg_tag msg)
  in
  match arity fs with
  | 0 -> eval []
  | n -> Proofview.tclUNIT (Tac2ffi.of_closure (Tac2val.abstract n eval))

let interp_escaped : string -> string = fun s ->
  let len = String.length s in
  let b = Buffer.create len in
  let rec loop escaped i =
    if i >= len then () else
    match (escaped, s.[i]) with
    | (false, '\\') -> loop true (i+1)
    | (false, c   ) -> Buffer.add_char b c   ; loop false (i+1)
    | (true , 'n' ) -> Buffer.add_char b '\n'; loop false (i+1)
    | (true , 't' ) -> Buffer.add_char b '\t'; loop false (i+1)
    | (true , '\\') -> Buffer.add_char b '\\'; loop false (i+1)
    | (true , _   ) -> loop false (i+1) (* Invalid escape: dropped. *)
  in
  loop false 0;
  Buffer.contents b

let msg_to_pp : msg -> Pp.t =
  let rec pp_item acc item =
    match item with
    | String(s)     ->
        let s = interp_escaped s in
        let rec add acc s =
          match s with
          | []                   -> acc
          | p :: []              -> Pp.app acc (Pp.str p)
          | p :: ((_ :: _) as s) ->
          let acc = Pp.app acc (Pp.str p) in
          let acc = Pp.app acc (Pp.fnl ()) in
          add acc s
        in
        add acc (String.split_on_char '\n' s)
    | Int(i)        -> Pp.app acc (Pp.int i)
    | Constr(s,e,c) ->
        begin
          try
            Pp.app acc (Printer.pr_econstr_env s e c)
          with e ->
            let msg =
              let e = Printexc.to_string e in
              Printf.sprintf "[ERROR %S when printing constr, printing AST:\n" e
            in
            let acc = Pp.app acc (Pp.str msg) in
            pp_item acc (Msg([Ast(c); String("\n]")]))
        end
    | Ast(c)        ->
        begin
          try
            let c = EConstr.Unsafe.to_constr c in
            Pp.app acc (Constr.debug_print c)
          with e ->
            let msg =
              let e = Printexc.to_string e in
              Printf.sprintf "[ERROR %S when printing constr AST]" e
            in
            Pp.app acc (Pp.str msg)
        end
    | Ident(i)      -> Pp.app acc (Names.Id.print i)
    | Msg(m)        -> List.fold_left pp_item acc m
    | Thunk(f)      -> pp_item acc (f ())
    | Pp(m)         -> Pp.app acc m
  in
  List.fold_left pp_item (Pp.mt ())

let msg_to_string : msg -> string = fun m ->
  Pp.string_of_ppcmds (msg_to_pp m)
