open Support

type indexed_theory =
  { file_path: Fpath.t
  ; theory: Dune_file.theory }

type transitive_dep_graph = string list StringMap.t

let build_theory_buckets files =
  List.fold_left
    (fun (theory_buckets, dependency_names) (file_path, theories) ->
      List.fold_left
        (fun (theory_buckets, dependency_names) (theory : Dune_file.theory) ->
          let theory_buckets =
            StringMap.update theory.name
              (function
                | None ->
                    Some [{file_path; theory}]
                | Some indexed_theories ->
                    Some ({file_path; theory} :: indexed_theories) )
              theory_buckets
          in
          let dependency_names =
            List.fold_left
              (fun dependency_names dependency ->
                StringSet.add dependency dependency_names )
              dependency_names theory.direct_dependencies
          in
          (theory_buckets, dependency_names) )
        (theory_buckets, dependency_names) theories )
    (StringMap.empty, StringSet.empty) files

let duplicate_names theory_buckets =
  StringMap.fold
    (fun name indexed_theories duplicates ->
      if List.length indexed_theories > 1 then StringSet.add name duplicates
      else duplicates )
    theory_buckets StringSet.empty

let dependency_locations theory_buckets name =
  match StringMap.find_opt name theory_buckets with
  | Some indexed_theories ->
      indexed_theories
      |> List.rev_map
           (fun indexed_theory -> "- " ^ Fpath.to_string indexed_theory.file_path)
      |> String.concat "\n"
  | None ->
      ""

let ambiguous_dependency_message theory_buckets ambiguous_names =
  let ambiguous_names = StringSet.elements ambiguous_names in
  match ambiguous_names with
  | [] ->
      assert false
  | [name] ->
      Printf.sprintf "Ambiguous theory dependency %S defined in:\n%s" name
        (dependency_locations theory_buckets name)
  | names ->
      let sections =
        List.map
          (fun name ->
            Printf.sprintf "%s:\n%s" name
              (dependency_locations theory_buckets name) )
          names
      in
      "Ambiguous theory dependencies defined in:\n"
      ^ String.concat "\n" sections

let unique_theories theory_buckets duplicate_names =
  StringMap.fold
    (fun name indexed_theories unique_theories ->
      if StringSet.mem name duplicate_names then unique_theories
      else
        match indexed_theories with
        | [indexed_theory] ->
            StringMap.add name indexed_theory unique_theories
        | _ ->
            failf "internal error: expected a unique theory named %S" name )
    theory_buckets StringMap.empty

let unresolved_dependency_message missing_dependencies =
  match missing_dependencies with
  | [] ->
      assert false
  | [dependency] ->
      Printf.sprintf "Unresolved theory dependency %S" dependency
  | dependencies ->
      Printf.sprintf "Unresolved theory dependencies %s"
        (String.concat ", " (List.map (Printf.sprintf "%S") dependencies))

let build_transitive_dep_graph files =
  let theory_buckets, dependency_names = build_theory_buckets files in
  let duplicate_names = duplicate_names theory_buckets in
  let ambiguous_dependencies =
    StringSet.inter dependency_names duplicate_names
  in
  if not (StringSet.is_empty ambiguous_dependencies) then
    failf "%s"
      (ambiguous_dependency_message theory_buckets ambiguous_dependencies) ;
  let dependency_map =
    unique_theories theory_buckets duplicate_names
    |> StringMap.map (fun indexed_theory ->
           dedupe_preserving_order indexed_theory.theory.direct_dependencies )
  in
  try Dependency_graph.transitive_closure dependency_map
  with
  | Dependency_graph.Incomplete_graph missing_dependencies ->
      failf "%s" (unresolved_dependency_message missing_dependencies)

let union_dependency_lists lists =
  List.fold_left
    (fun dependencies new_dependencies ->
      dedupe_preserving_order (dependencies @ new_dependencies) )
    [] lists

let inherited_dependencies (graph : transitive_dep_graph) direct_dependencies =
  List.map
    (fun dependency ->
      match StringMap.find_opt dependency graph with
      | Some dependencies ->
          dependencies
      | None ->
          [] )
    direct_dependencies
  |> union_dependency_lists

let updated_dependencies (graph : transitive_dep_graph)
    (theory : Dune_file.theory) =
  let direct_dependencies = theory.direct_dependencies in
  let all_dependencies =
    match StringMap.find_opt theory.name graph with
    | Some dependencies ->
        dependencies
    | None ->
        dedupe_preserving_order
          (direct_dependencies
          @ inherited_dependencies graph direct_dependencies)
  in
  let direct_dependency_set = StringSet.of_list direct_dependencies in
  let transitive_dependencies =
    List.filter
      (fun dependency -> not (StringSet.mem dependency direct_dependency_set))
      all_dependencies
  in
  (direct_dependencies, transitive_dependencies)

let same_dependency_set
    (original_direct_dependencies, original_transitive_dependencies)
    (updated_direct_dependencies, updated_transitive_dependencies) =
  let original =
    StringSet.of_list
      (original_direct_dependencies @ original_transitive_dependencies)
  in
  let updated =
    StringSet.of_list
      (updated_direct_dependencies @ updated_transitive_dependencies)
  in
  StringSet.equal original updated

(** [normalize graph (direct_dependencies, transitive_dependencies)] applies
    the normal rewriting policy to an already computed dependency pair.

    Normalization rules:
    - the direct dependencies are preserved exactly as given
    - the transitive dependencies are deduplicated and sorted alphabetically
    - dependencies that are already direct are not moved by this function;
      callers are expected to compute the direct/transitive split first *)
let normalize (_graph : transitive_dep_graph)
    (direct_dependencies, transitive_dependencies) =
  (direct_dependencies, dedupe_sorted transitive_dependencies)

let preserve_existing_order original_transitive_dependencies
    (direct_dependencies, transitive_dependencies) =
  let existing_transitive =
    dedupe_preserving_order original_transitive_dependencies
  in
  let computed_set = StringSet.of_list transitive_dependencies in
  let retained_existing =
    List.filter
      (fun dependency -> StringSet.mem dependency computed_set)
      existing_transitive
  in
  let retained_existing_set = StringSet.of_list retained_existing in
  let appended_new =
    List.filter
      (fun dependency -> not (StringSet.mem dependency retained_existing_set))
      transitive_dependencies
  in
  (direct_dependencies, retained_existing @ appended_new)

let compute_updated_theory (graph : transitive_dep_graph) ~no_normalize
    (theory : Dune_file.theory) =
  let updated_dependencies =
    updated_dependencies graph theory
  in
  if
    same_dependency_set
      (theory.direct_dependencies, theory.transitive_dependencies)
      updated_dependencies
  then theory
  else
    let direct_dependencies, transitive_dependencies =
      if no_normalize then
        preserve_existing_order theory.transitive_dependencies
          updated_dependencies
      else normalize graph updated_dependencies
    in
    {theory with direct_dependencies; transitive_dependencies}

let update_theories graph ~no_normalize theories =
  List.map
    (fun (theory : Dune_file.theory) ->
      try compute_updated_theory graph ~no_normalize theory
      with Error message ->
        failf "[%s]: %s" theory.name message )
    theories
