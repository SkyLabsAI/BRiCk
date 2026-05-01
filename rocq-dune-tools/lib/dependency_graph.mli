exception Incomplete_graph of string list

val transitive_closure :
  string list Support.StringMap.t -> string list Support.StringMap.t
(** [transitive_closure dependencies] returns a map with the same keys as
    [dependencies] where each dependency list has been expanded to include the
    full transitive closure of that key's dependencies.

    The input map is interpreted as a directed graph: each key names a node,
    and its associated list gives the node's direct dependencies. The returned
    lists are expected to contain the dependencies reachable from each key via
    repeated graph traversal.

    If any dependency name appears in a dependency list but is not itself a
    key in [dependencies], this function raises an exception carrying the
    sorted list of missing dependency names. *)
