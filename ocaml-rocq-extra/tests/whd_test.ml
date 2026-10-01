(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Rocq_extra.Extra

let assert_equal label sigma expected actual =
  if not (EConstr.eq_constr sigma expected actual) then
    failwith ("Whd.eval: " ^ label)

let () =
  let env = Environ.empty_env in
  let sigma = Evd.from_env env in
  let typ = EConstr.mkSort (EConstr.ESorts.make Sorts.set) in
  let value = EConstr.mkInt (Uint63.of_int 7) in
  let identity = EConstr.mkLambda (EConstr.anonR, typ, EConstr.mkRel 1) in
  let beta_redex = EConstr.mkApp (identity, [| value |]) in
  let zeta_redex =
    EConstr.mkLetIn (EConstr.anonR, value, typ, EConstr.mkRel 1)
  in
  let whd = Whd.eval env sigma RedFlags.all in
  assert_equal "beta" sigma value (whd beta_redex);
  assert_equal "zeta with reused state" sigma value (whd zeta_redex);

  let no_reduction = Whd.eval env sigma RedFlags.no_red in
  assert_equal "reduction flags" sigma beta_redex (no_reduction beta_redex);

  let safe_application = EConstr.mkApp (typ, [| value |]) in
  assert_equal "syntactic WHNF" sigma safe_application (whd safe_application);

  let sigma, evar = Evarutil.new_evar env sigma typ in
  let evar_key =
    match EConstr.kind sigma evar with
    | Constr.Evar (key, _) -> key
    | _ -> assert false
  in
  let sigma = Evd.define evar_key value sigma in
  let whd = Whd.eval env sigma RedFlags.all in
  assert_equal "instantiated evar" sigma value (whd evar);

  List.iter
    (fun share ->
      let whd = Whd.eval ?share env sigma RedFlags.all in
      assert_equal "sharing override" sigma value (whd beta_redex))
    [ None; Some false; Some true ]
