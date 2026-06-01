open Support

type t = {root: Fpath.t}

let normalize_workspace_root ~cwd ~source ~value =
  let root =
    fpath_or_fail
      ~context:(Printf.sprintf "invalid workspace root from %s" source)
      value
  in
  let root =
    (if Fpath.is_rel root then Fpath.append cwd root else root)
    |> Fpath.to_dir_path |> Fpath.normalize
  in
  let root =
    result_or_fail
      ~context:
        (Printf.sprintf "failed to canonicalize workspace root from %s" source)
      (OS.Path.realpath root)
    |> Fpath.to_dir_path |> Fpath.normalize
  in
  if not (is_within ~root cwd) then
    failf "current directory %s is not inside workspace root %s from %s"
      (Fpath.to_string cwd) (Fpath.to_string root) source ;
  root

let current_workspace_from_env cwd =
  let rec loop = function
    | [] ->
        None
    | name :: rest -> (
      match env_var name with
      | Some value ->
          Some {root= normalize_workspace_root ~cwd ~source:name ~value}
      | None ->
          loop rest )
  in
  loop ["DUNE_SOURCEROOT"; "DUNE_ROOT"]

let path_exists path =
  result_or_fail
    ~context:(Printf.sprintf "failed to stat %s" (Fpath.to_string path))
    (OS.Path.exists path)

let directory_has_workspace_marker dir =
  List.exists
    (fun marker -> path_exists Fpath.(dir / marker))
    ["dune-workspace"; "dune-project"]

let rec find_workspace_root_by_walk dir =
  if directory_has_workspace_marker dir then Some dir
  else
    let parent = Fpath.parent dir |> Fpath.to_dir_path |> Fpath.normalize in
    if Fpath.equal parent dir then None else find_workspace_root_by_walk parent

let current () =
  let cwd = current_cwd () in
  match current_workspace_from_env cwd with
  | Some workspace ->
      workspace
  | None -> (
    match find_workspace_root_by_walk cwd with
    | Some root ->
        {root}
    | None ->
        failf
          "no dune workspace root was found: set DUNE_SOURCEROOT or DUNE_ROOT, \
           or run from inside a tree containing a dune-workspace or \
           dune-project file (searched from %s upward)"
          (Fpath.to_string cwd) )

let root workspace = workspace.root

let dune_files workspace =
  let root = workspace.root in
  let stop_on_error _path = function
    | Ok _ ->
        Ok ()
    | Error _ as error ->
        error
  in
  let traverse path =
    Ok (not (StringSet.mem (Fpath.basename path) prune_dirs))
  in
  let collect path acc =
    if String.equal (Fpath.basename path) "dune" then path :: acc else acc
  in
  result_or_fail
    ~context:(Printf.sprintf "failed to scan %s" (Fpath.to_string root))
    (OS.Path.fold ~err:stop_on_error ~dotfiles:false ~elements:`Files
       ~traverse:(`Sat traverse) collect []
       [Fpath.to_dir_path root] )
  |> List.sort Fpath.compare
