open Support

exception Incomplete_graph of string list

let transitive_closure dependencies =
  let known_dependencies =
    StringMap.fold
      (fun dependency _ known -> StringSet.add dependency known)
      dependencies StringSet.empty
  in
  let missing_dependencies =
    StringMap.fold
      (fun _ direct_dependencies missing ->
        List.fold_left
          (fun missing dependency ->
            if StringSet.mem dependency known_dependencies then missing
            else StringSet.add dependency missing )
          missing direct_dependencies )
      dependencies StringSet.empty
  in
  if not (StringSet.is_empty missing_dependencies) then
    raise (Incomplete_graph (StringSet.elements missing_dependencies)) ;
  let dependency_path path_rev name =
    List.rev (name :: path_rev) |> String.concat " -> "
  in
  let cache = Hashtbl.create (StringMap.cardinal dependencies) in
  let rec expand ~path_rev ~visiting name =
    if StringSet.mem name visiting then
      failf "Dependency cycle detected: %s" (dependency_path path_rev name) ;
    match Hashtbl.find_opt cache name with
    | Some closure ->
        closure
    | None ->
        let direct_dependencies =
          match StringMap.find_opt name dependencies with
          | Some direct_dependencies ->
              dedupe_preserving_order direct_dependencies
          | None ->
              raise (Incomplete_graph [name])
        in
        let visiting = StringSet.add name visiting in
        let closure =
          List.fold_left
            (fun closure dependency ->
              let closure =
                append_unique_preserving_order closure [dependency]
              in
              append_unique_preserving_order closure
                (expand ~path_rev:(name :: path_rev) ~visiting dependency) )
            [] direct_dependencies
        in
        Hashtbl.replace cache name closure ;
        closure
  in
  StringMap.mapi
    (fun name _ -> expand ~path_rev:[] ~visiting:StringSet.empty name)
    dependencies
