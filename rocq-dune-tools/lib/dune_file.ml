open Support

exception Theory_mismatch of string list

type theory_id = int

type theory =
  { id: theory_id
  ; name: string
  ; direct_dependencies: string list
  ; transitive_dependencies: string list }

type span =
  { start: int
  ; finish: int }

type stanza =
  { theory: theory
  ; theory_span: span
  ; theories_span: span option }

type t =
  { text: string
  ; stanzas: stanza list }

let substring text span = String.sub text span.start (span.finish - span.start)

let skip_comment text index =
  let length = String.length text in
  let rec loop i =
    if i >= length || Char.equal text.[i] '\n' then i else loop (i + 1)
  in
  loop index

let skip_string text index =
  let length = String.length text in
  let rec loop i =
    if i >= length then failf "Unterminated string literal"
    else if Char.equal text.[i] '\\' then loop (i + 2)
    else if Char.equal text.[i] '"' then i + 1
    else loop (i + 1)
  in
  loop (index + 1)

(* Sexplib gives us structure, but not source locations. This small scanner is
   only for finding list spans so we can rewrite just the (theories ...) form
   without reserializing the entire dune file. *)
let list_spans text ~offset =
  let length = String.length text in
  let rec loop index depth start acc =
    if index >= length then
      if depth <> 0 then failf "Unterminated list expression" else List.rev acc
    else
      let char = text.[index] in
      if Char.equal char ';' then loop (skip_comment text index) depth start acc
      else if Char.equal char '"' then
        loop (skip_string text index) depth start acc
      else if Char.equal char '(' then
        let start = if depth = 0 then Some index else start in
        loop (index + 1) (depth + 1) start acc
      else if Char.equal char ')' then
        if depth = 0 then failf "Unexpected closing parenthesis"
        else
          let depth = depth - 1 in
          let index = index + 1 in
          if depth = 0 then
            match start with
            | Some start ->
                loop index depth None
                  ({start= offset + start; finish= offset + index} :: acc)
            | None ->
                failf "internal error: missing start while collecting list span"
          else loop index depth start acc
      else loop (index + 1) depth start acc
  in
  loop 0 0 None []

let tokenize_atoms text =
  let length = String.length text in
  let rec loop index acc =
    if index >= length then List.rev acc
    else
      let char = text.[index] in
      if Char.equal char ';' then loop (skip_comment text index) acc
      else if Char.equal char '"' then
        let finish = skip_string text index in
        loop finish (String.sub text index (finish - index) :: acc)
      else if
        Char.equal char '(' || Char.equal char ')' || Char.equal char ' '
        || Char.equal char '\n' || Char.equal char '\t' || Char.equal char '\r'
      then loop (index + 1) acc
      else
        let rec advance i =
          if i >= length then i
          else
            let char = text.[i] in
            if
              Char.equal char ';' || Char.equal char '(' || Char.equal char ')'
              || Char.equal char ' ' || Char.equal char '\n'
              || Char.equal char '\t' || Char.equal char '\r'
            then i
            else advance (i + 1)
        in
        let finish = advance index in
        loop finish (String.sub text index (finish - index) :: acc)
  in
  loop 0 []

let line_is_transitive_marker line =
  String.equal (String.trim line) transitive_marker

let split_theories_dependencies theories_text listed_dependencies =
  let lines = String.split_on_char '\n' theories_text in
  let rec split prefix = function
    | [] ->
        None
    | line :: rest when line_is_transitive_marker line ->
        Some (List.rev prefix, rest)
    | line :: rest ->
        split (line :: prefix) rest
  in
  match split [] lines with
  | None ->
      (listed_dependencies, [])
  | Some (prefix_lines, suffix_lines) ->
      if List.exists line_is_transitive_marker suffix_lines then
        failf "Multiple transitive dependency markers in theories stanza" ;
      let direct_tokens = tokenize_atoms (String.concat "\n" prefix_lines) in
      let direct_dependencies =
        match direct_tokens with
        | "theories" :: dependencies ->
            dependencies
        | _ ->
            failf "Could not recover direct dependencies from theories stanza"
      in
      let transitive_dependencies =
        tokenize_atoms (String.concat "\n" suffix_lines)
      in
      (direct_dependencies, transitive_dependencies)

let is_named_list name = function
  | Sexp.List (Sexp.Atom head :: _) ->
      String.equal head name
  | _ ->
      false

let find_field name = function
  | Sexp.List (_ :: items) ->
      let rec loop = function
        | Sexp.List (Sexp.Atom head :: tail) :: _
          when String.equal head name ->
            Some tail
        | _ :: rest ->
            loop rest
        | [] ->
            None
      in
      loop items
  | _ ->
      None

let atom_or_fail ~context = function
  | Sexp.Atom atom ->
      atom
  | sexp ->
      failf "%s: expected atom, got %s" context (Sexp.to_string_hum sexp)

let find_child_list_span form_text name =
  let body_text = String.sub form_text 1 (String.length form_text - 2) in
  let spans = list_spans body_text ~offset:1 in
  let rec loop = function
    | [] ->
        None
    | span :: rest ->
        let child_text = substring form_text span in
        let child_form =
          parse_sexp ~context:("invalid child form for " ^ name) child_text
        in
        if is_named_list name child_form then Some span else loop rest
  in
  loop spans

let theory_of_stanza id file_path theory_span text form =
  let name =
    match find_field "name" form with
    | Some [atom] ->
        atom_or_fail ~context:"invalid rocq.theory name" atom
    | _ ->
        failf "%s: rocq.theory stanza is missing a single (name ...) field"
          (Fpath.to_string file_path)
  in
  let theories_span = find_child_list_span text "theories" in
  let direct_dependencies, transitive_dependencies =
    match theories_span with
    | None ->
        ([], [])
    | Some theories_span ->
        let theories_field =
          match find_field "theories" form with
          | Some theories_field ->
              theories_field
          | None ->
              failf
                "%s: found theories span but could not parse theories field"
                (Fpath.to_string file_path)
        in
        let listed_dependencies =
          List.map
            (atom_or_fail
               ~context:
                 (Printf.sprintf "invalid theory dependency in %s"
                    (Fpath.to_string file_path) ) )
            theories_field
        in
        let theories_text = substring text theories_span in
        split_theories_dependencies theories_text listed_dependencies
  in
  { theory=
      {id; name; direct_dependencies; transitive_dependencies}
  ; theory_span
  ; theories_span }

let read file_path =
  let text = read_text_file file_path in
  let spans = list_spans text ~offset:0 in
  let stanzas =
    List.filter_map
      (fun (id, theory_span) ->
        let form_text = substring text theory_span in
        let form =
          parse_sexp
            ~context:
              (Printf.sprintf "invalid form in %s" (Fpath.to_string file_path))
            form_text
        in
        if not (is_named_list "rocq.theory" form) then None
        else Some (theory_of_stanza id file_path theory_span form_text form) )
      (List.mapi (fun index span -> (index, span)) spans)
  in
  let file = {text; stanzas} in
  (file, List.map (fun stanza -> stanza.theory) stanzas)

let line_indent text index =
  let rec loop i =
    if i < 0 then 0 else if Char.equal text.[i] '\n' then i + 1 else loop (i - 1)
  in
  let line_start = loop (index - 1) in
  String.sub text line_start (index - line_start)

let wrap_dependency_lines prefix dependencies =
  match dependencies with
  | [] ->
      []
  | first :: rest ->
      let rec loop current acc = function
        | [] ->
            List.rev (current :: acc)
        | dependency :: remaining ->
            let candidate = current ^ " " ^ dependency in
            if String.length candidate <= 80 then
              loop candidate acc remaining
            else loop (prefix ^ dependency) (current :: acc) remaining
      in
      loop (prefix ^ first) [] rest

let format_theories_block indent direct_dependencies transitive_dependencies =
  if direct_dependencies = [] && transitive_dependencies = [] then "(theories)"
  else
    let transitive_section =
      if transitive_dependencies = [] then []
      else
        (indent ^ " " ^ transitive_marker)
        :: wrap_dependency_lines (indent ^ " ") transitive_dependencies
    in
    String.concat "\n"
      ( ["(theories"]
      @ List.map (fun dependency -> indent ^ " " ^ dependency) direct_dependencies
      @ transitive_section
      @ [indent ^ ")"] )

let apply_replacements text replacements =
  let replacements =
    List.sort
      (fun (left, _) (right, _) -> Int.compare right.start left.start)
      replacements
  in
  List.fold_left
    (fun updated (span, replacement) ->
      let prefix = String.sub updated 0 span.start in
      let suffix =
        String.sub updated span.finish (String.length updated - span.finish)
      in
      prefix ^ replacement ^ suffix )
    text replacements

let mismatch names = raise (Theory_mismatch (dedupe_sorted names))

let validate_theories file theories =
  let expected_theories = List.map (fun stanza -> stanza.theory) file.stanzas in
  let expected_by_id =
    List.fold_left
      (fun theories_by_id (theory : theory) ->
        StringMap.add (string_of_int theory.id) theory theories_by_id )
      StringMap.empty expected_theories
  in
  let provided_by_id, duplicate_names =
    List.fold_left
      (fun (theories_by_id, duplicate_names) (theory : theory) ->
        let key = string_of_int theory.id in
        if StringMap.mem key theories_by_id then
          (theories_by_id, theory.name :: duplicate_names)
        else (StringMap.add key theory theories_by_id, duplicate_names) )
      (StringMap.empty, []) theories
  in
  let mismatch_names =
    List.fold_left
      (fun names expected ->
        let key = string_of_int expected.id in
        match StringMap.find_opt key provided_by_id with
        | Some (provided : theory) when String.equal provided.name expected.name ->
            names
        | Some (provided : theory) ->
            expected.name :: provided.name :: names
        | None ->
            expected.name :: names )
      duplicate_names expected_theories
  in
  let mismatch_names =
    StringMap.fold
      (fun key (theory : theory) names ->
        if StringMap.mem key expected_by_id then names else theory.name :: names)
      provided_by_id mismatch_names
  in
  if mismatch_names <> [] then mismatch mismatch_names ;
  provided_by_id

let write file theories =
  let theories_by_id = validate_theories file theories in
  let replacements =
    List.filter_map
      (fun stanza ->
        let theory =
          match StringMap.find_opt (string_of_int stanza.theory.id) theories_by_id with
          | Some theory ->
              theory
          | None ->
              mismatch [stanza.theory.name]
        in
        if theory == stanza.theory then None
        else
          match stanza.theories_span with
          | None ->
              if
                theory.direct_dependencies <> []
                || theory.transitive_dependencies <> []
              then
                failf
                  "[%s]: computed non-empty dependencies but found no \
                   (theories ...) field"
                  theory.name ;
              None
          | Some theories_span ->
              let absolute_span =
                { start= stanza.theory_span.start + theories_span.start
                ; finish= stanza.theory_span.start + theories_span.finish }
              in
              let indent = line_indent file.text absolute_span.start in
              let replacement =
                format_theories_block indent theory.direct_dependencies
                  theory.transitive_dependencies
              in
              Some (absolute_span, replacement) )
      file.stanzas
  in
  apply_replacements file.text replacements
