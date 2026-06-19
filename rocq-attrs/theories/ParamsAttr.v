(** Load this module to enable the [#[params="N"]] attribute and the
    generated [Params] instances.

    This file loads [Stdlib.Classes.Morphisms] and registers its [Params]
    class for the plugin under the private key [rocq_attrs.params.type].

    Plugin-local support covers [Definition] and section [Let] (local-only).
    Other declaration commands need Rocq-core hook plumbing; do not rely on
    [#[params]] there yet. *)
From Stdlib.Classes Require Export Morphisms.

Register Params as rocq_attrs.params.type.

Declare ML Module "rocq-attrs.params".
