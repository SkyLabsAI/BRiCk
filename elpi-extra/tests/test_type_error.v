(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require skylabs.elpi.extra.extra.

(** Confirm that we made warnings from <<Elpi Typecheck>> fatal. *)

Elpi Program test lp:{{ }}.
Fail Elpi Accumulate lp:{{
  undeclared_constant cats.
}}.


Fail Elpi Accumulate lp:{{
  type cats dogs.
  type undeclared_constant dogs -> prop.

  undeclared_constant cats.
}}.

Fail Elpi Accumulate lp:{{
  type cats dogs.
  type undeclared_constant dogs -> prop.

  undeclared_constant cats.
}}.

Succeed Elpi Accumulate lp:{{
  kind dogs type.
  type cats dogs.
  type undeclared_constant dogs -> prop.

  undeclared_constant cats.
}}.

