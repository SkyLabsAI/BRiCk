(** Transitive dependency closure indexed by theory name. Each entry contains
    the theory's direct and transitive dependencies, with direct dependencies
    appearing before any inherited transitive dependencies. *)
type transitive_dep_graph = string list Support.StringMap.t

val build_transitive_dep_graph :
  (Fpath.t * Dune_file.theory list) list -> transitive_dep_graph
(** Build the transitive dependency graph for all uniquely named theories.

    Direct dependencies are taken from [Dune_file.read], except implicit
    dependencies such as [Corelib] are ignored because they never need to be
    listed explicitly. Duplicate theory names are tolerated unless they are
    referenced as dependencies. If a duplicate name is referenced, this
    function raises an ambiguity error with source locations. *)

val normalize : string list * string list -> string list * string list
(** [normalize (direct_dependencies, transitive_dependencies)] applies the
    normal rewriting policy to an already computed dependency pair.

    Normalization rules:
    - the direct dependencies are preserved exactly as given
    - the transitive dependencies are deduplicated and sorted alphabetically
    - dependencies that are already direct are not moved by this function;
      callers are expected to compute the direct/transitive split first *)

val update_theories :
     transitive_dep_graph
  -> no_normalize:bool
  -> Dune_file.theory list
  -> Dune_file.theory list
(** Update a list of theories using a previously computed transitive dependency
    graph.

    For each theory, direct dependencies are treated as authoritative roots,
    except implicit dependencies such as [Corelib] are removed. The updated
    transitive dependencies are computed either from the theory's own graph
    entry, or, when the theory name is absent from the graph because duplicates
    were removed, by unioning the closures of its direct dependencies. If the
    overall dependency set is unchanged, the original theory value is returned
    unchanged so no file rewrite is needed. *)
