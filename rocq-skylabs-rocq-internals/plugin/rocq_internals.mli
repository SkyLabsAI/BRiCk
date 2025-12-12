(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type pat = Pattern.constr_pattern

val eta_reduce_pat : pat -> pat

val decomp_pat : pat -> pat * pat list

module Patternops : sig
  val occurn_pattern_meta_closed : int -> Pattern.constr_pattern -> bool
  val noccurn_pattern_meta_closed : int -> Pattern.constr_pattern -> bool
end

val evaluable_constant : Names.Constant.t -> Environ.env ->
  TransparentState.t -> bool

val evaluable_named : Names.variable -> Environ.env ->
  TransparentState.t -> bool
