(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

let definitely_whnf : EConstr.t -> bool =
  let rec go under_app term =
    match Constr.kind term with
    | Constr.App (head, _) -> go true head
    | Constr.Lambda _ | Constr.Fix _ -> not under_app
    | Constr.Meta _
    | Constr.Sort _
    | Constr.Prod _
    | Constr.Ind _
    | Constr.Construct _
    | Constr.Int _
    | Constr.Float _
    | Constr.String _
    | Constr.Array _ -> true
    | Constr.Var _
    | Constr.Rel _
    | Constr.Evar _
    | Constr.Cast _
    | Constr.LetIn _
    | Constr.Const _
    | Constr.Case _
    | Constr.CoFix _
    | Constr.Proj _
    (* A block can still need reduction of its hidden captures. *)
    | Constr.PBlock _
    | Constr.PRun _ -> false
  in
  fun term -> go false (EConstr.Unsafe.to_constr term)

let eval ?share env sigma reds =
  let reduction = Lazy.from_fun @@ fun () ->
    let env =
      match share with
      | None -> env
      | Some share_reduction ->
        let typing_flags = Environ.typing_flags env in
        Environ.set_typing_flags
          { typing_flags with Declarations.share_reduction }
          env
    in
    let evars = Evd.evar_handler sigma in
    let univs = Evd.universes sigma in
    let infos = CClosure.create_clos_infos ~univs ~evars reds env in
    (infos, CClosure.create_tab ())
  in
  fun term ->
    if definitely_whnf term then term
    else
      let term = EConstr.Unsafe.to_constr term in
      let infos, table = Lazy.force reduction in
      EConstr.of_constr (CClosure.whd_val infos table (CClosure.inject term))
