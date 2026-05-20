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

type parsed_form =
  { span: span
  ; form: Sexp.t
  ; annotated_form: Sexp.Annotated.t }

let substring text span = String.sub text span.start (span.finish - span.start)

let is_whitespace = function ' ' | '\n' | '\t' | '\r' -> true | _ -> false

let is_atom_delimiter = function
  | ';' | '(' | ')' ->
      true
  | char ->
      is_whitespace char

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

let span_of_range (range : Sexp.Annotated.range) =
  {start= range.start_pos.offset; finish= range.end_pos.offset + 1}

let parse_annotated_forms ~context text =
  try
    Sexp.Annotated.of_string_many text
    |> List.map (fun annotated_form ->
        { span= Sexp.Annotated.get_range annotated_form |> span_of_range
        ; form= Sexp.Annotated.get_sexp annotated_form
        ; annotated_form } )
  with exn -> failf "%s: %s" context (Printexc.to_string exn)

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
      else if is_atom_delimiter char then loop (index + 1) acc
      else
        let rec advance i =
          if i >= length then i
          else
            let char = text.[i] in
            if is_atom_delimiter char then i else advance (i + 1)
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
        | Sexp.List (Sexp.Atom head :: tail) :: _ when String.equal head name ->
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

let find_child_list_span parent_span annotated_form name =
  let rec loop = function
    | [] ->
        None
    | child :: rest ->
        let child_form = Sexp.Annotated.get_sexp child in
        if is_named_list name child_form then
          let child_span = Sexp.Annotated.get_range child |> span_of_range in
          Some
            { start= child_span.start - parent_span.start
            ; finish= child_span.finish - parent_span.start }
        else loop rest
  in
  match annotated_form with
  | Sexp.Annotated.List (_, children, _) ->
      loop children
  | Sexp.Annotated.Atom _ ->
      None

let theory_of_stanza id file_path file_text parsed_form =
  let text = substring file_text parsed_form.span in
  let form = parsed_form.form in
  let name =
    match find_field "name" form with
    | Some [atom] ->
        atom_or_fail ~context:"invalid rocq.theory name" atom
    | _ ->
        failf "%s: rocq.theory stanza is missing a single (name ...) field"
          (Fpath.to_string file_path)
  in
  let theories_span =
    find_child_list_span parsed_form.span parsed_form.annotated_form "theories"
  in
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
              failf "%s: found theories span but could not parse theories field"
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
  { theory= {id; name; direct_dependencies; transitive_dependencies}
  ; theory_span= parsed_form.span
  ; theories_span }

let read file_path =
  let text = read_text_file file_path in
  let parsed_forms =
    parse_annotated_forms
      ~context:(Printf.sprintf "invalid form in %s" (Fpath.to_string file_path))
      text
  in
  let stanzas =
    List.filter_map
      (fun (id, parsed_form) ->
        if not (is_named_list "rocq.theory" parsed_form.form) then None
        else Some (theory_of_stanza id file_path text parsed_form) )
      (List.mapi (fun index parsed_form -> (index, parsed_form)) parsed_forms)
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
            if String.length candidate <= 80 then loop candidate acc remaining
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
      @ List.map
          (fun dependency -> indent ^ " " ^ dependency)
          direct_dependencies
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
        IntMap.add theory.id theory theories_by_id )
      IntMap.empty expected_theories
  in
  let provided_by_id, duplicate_names =
    List.fold_left
      (fun (theories_by_id, duplicate_names) (theory : theory) ->
        if IntMap.mem theory.id theories_by_id then
          (theories_by_id, theory.name :: duplicate_names)
        else (IntMap.add theory.id theory theories_by_id, duplicate_names) )
      (IntMap.empty, []) theories
  in
  let mismatch_names =
    List.fold_left
      (fun names expected ->
        match IntMap.find_opt expected.id provided_by_id with
        | Some (provided : theory) when String.equal provided.name expected.name
          ->
            names
        | Some (provided : theory) ->
            expected.name :: provided.name :: names
        | None ->
            expected.name :: names )
      duplicate_names expected_theories
  in
  let mismatch_names =
    IntMap.fold
      (fun id (theory : theory) names ->
        if IntMap.mem id expected_by_id then names else theory.name :: names )
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
          match IntMap.find_opt stanza.theory.id theories_by_id with
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
