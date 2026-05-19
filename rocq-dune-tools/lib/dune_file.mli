(** Raised by {!write} when the supplied theories do not match the theories
    returned by {!read}. The payload carries the sorted theory names that were
    missing, unexpected, or renamed. *)
exception Theory_mismatch of string list

(** Opaque representation of a parsed dune file together with the source
    locations needed to write dependency updates back into the original text. *)
type t

(** Stable identifier for a specific [rocq.theory] stanza within a parsed dune
    file. Values are produced by {!read} and are intended to be passed back to
    {!write}. *)
type theory_id

(** Semantic view of a [rocq.theory] stanza.

    For a flat [(theories ...)] stanza, [direct_dependencies] contains the
    listed dependencies and [transitive_dependencies] is empty. For a stanza
    already written in the direct/transitive style, [direct_dependencies]
    contains the dependencies before the marker and [transitive_dependencies]
    contains the dependencies after it. *)
type theory =
  { id: theory_id
  ; name: string
  ; direct_dependencies: string list
  ; transitive_dependencies: string list }

val read : Fpath.t -> t * theory list
(** [read path] parses [path] and extracts the dependency information from each
    [rocq.theory] stanza in file order. *)

val write : t -> theory list -> string
(** [write file theories] returns updated dune file text with the supplied
    dependencies written back into the original file.

    The [theories] list must describe exactly the same stanzas returned by
    {!read}, matched by [id] and [name]. If it does not, this function raises
    {!Theory_mismatch}. *)
