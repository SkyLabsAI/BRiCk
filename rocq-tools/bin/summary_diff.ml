(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

let use_colors : bool ref = ref true

(** Format transformers (colors). *)
let with_color k fmt =
  (if !use_colors then "\027["^^k^^"m" ^^ fmt ^^ "\027[0m" else fmt) ^^ "%!"

let red    fmt = with_color "31" fmt
let green  fmt = with_color "32" fmt

let info : 'a outfmt -> 'a = fun fmt ->
  Format.printf (fmt ^^ "%!")

let einfo : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (fmt ^^ "%!")

let panic : ('a, 'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter
    (red ("[Panic] " ^^ fmt ^^ "\n"))

(** [fold_file csv_file f acc] folds function [f] over the lines of given file
    [csv_file], starting with accumulator value [acc]. All lines are parsed as
    a CSV data line, and are expected to have at least two fields: a file name
    and an instruction count. The function panics in case of file system error
    or parse error. *)
let fold_file : string -> (string -> int -> 'a -> 'a) -> 'a -> 'a =
    fun csv_file f acc ->
  let rec fold i ic acc =
    let error msg = panic "Error in file %s, line %i: %s." csv_file i msg in
    match In_channel.input_line ic with
    | None       -> acc
    | Some(line) ->
    let (file, instr) =
      match String.split_on_char ',' line with
      | file :: instr :: _ -> (String.trim file, String.trim instr)
      | _                  -> error "bad number of fields"
    in
    let instr =
      try int_of_string instr with Failure(_) ->
      error "instruction count does not look like an integer"
    in
    fold (i+1) ic (f file instr acc)
  in
  try
    In_channel.with_open_text csv_file @@ fun ic ->
    ignore (In_channel.input_line ic); (* Skipping header. *)
    fold 1 ic acc
  with Sys_error(s) ->
    panic "Error with file %s: %s." csv_file s

(** [is_cpp2v file] indicates whether the given file name [file] looks like it
    corresponds to an AST file (as produced by the cpp2v program). *)
let is_cpp2v : string -> bool = fun file ->
  String.ends_with ~suffix:"_hpp.v"       file ||
  String.ends_with ~suffix:"_cpp.v"       file ||
  String.ends_with ~suffix:"_hpp_names.v" file ||
  String.ends_with ~suffix:"_cpp_names.v" file

module S = Set.Make(String)
module M = Map.Make(String)

(** Performance data. *)
module Data : sig
  (** Performance data for a single Rocq file. *)
  type t = {
    file : string;
    (** Rocq file corresponding to this entry. *)
    is_cpp2v : bool;
    (** Does this file look like an AST file based on its name? *)
    instr_ref : int option;
    (** Reference instruction count, if any. *)
    instr : int option;
    (** Instruction count for the changes, if any. *)
  }

  (** [get ~ref_data ~new_data] gathers performance data from the given files,
      which are all expected to contain CSV data. Argument [ref_data] provides
      the reference data (to be compared to), and [new_data] holds potentially
      several versions of the data to be compared (entries of later files take
      precedence over entries in earlier file in the list order). The function
      panics upon errors (either file-system-related, or parsing error). *)
  val get : ref_data:string -> new_data:string list -> t M.t
end = struct
  type t = {
    file : string;
    is_cpp2v : bool;
    instr_ref : int option;
    instr : int option;
  }

  let get ~ref_data ~new_data =
    let m =
      let init file instr m =
        let is_cpp2v = is_cpp2v file in
        M.add file {file; is_cpp2v; instr_ref = Some(instr); instr = None} m
      in
      fold_file ref_data init M.empty
    in
    let add m new_data =
      let add file instr m =
        let update datao =
          match datao with
          | Some(data) -> Some({data with instr = Some(instr)})
          | None       ->
          let is_cpp2v = is_cpp2v file in
          Some({file; is_cpp2v; instr_ref = None; instr = Some(instr)})
        in
        M.update file update m
      in
      fold_file new_data add m
    in
    List.fold_left add m new_data
end

type instr_count = int

type 'a by_type = {
  bt_total: 'a;
  bt_cpp2v: 'a;
  bt_other: 'a;
}

let bt_add fname (bt : instr_count by_type) (v : instr_count) =
  if is_cpp2v fname then
    {bt with
     bt_total = bt.bt_total + v;
     bt_cpp2v = bt.bt_cpp2v + v;}
  else
    {bt with
     bt_total = bt.bt_total + v;
     bt_other = bt.bt_other + v;}

let bt_zero : instr_count by_type = { bt_total = 0; bt_cpp2v = 0; bt_other = 0 }

type diff = int * float

let negate_diff (i, f) = (-i, -.f)

let make_diff : instr_count -> instr_count -> diff = fun ic_ref ic_new ->
  let diff_abs = ic_new - ic_ref in
  (diff_abs, float_of_int (100 * diff_abs) /. float_of_int ic_ref)

let bt_make_diff : instr_count by_type -> instr_count by_type -> diff by_type =
    fun ic_ref ic_new ->
  let bt_total = make_diff ic_ref.bt_total ic_new.bt_total in
  let bt_cpp2v = make_diff ic_ref.bt_cpp2v ic_new.bt_cpp2v in
  let bt_other = make_diff ic_ref.bt_other ic_new.bt_other in
  { bt_total; bt_cpp2v; bt_other }

type analysis = {
  total_ref : instr_count by_type;
  total_new : instr_count by_type;
  total_diff : diff by_type;
  num_disappeared : int;
  total_disappeared : diff;
  num_appeared : int;
  total_appeared : diff;
  per_file : (string * (bool * (instr_count * instr_count * diff))) list;
}

let pp_analysis : Format.formatter -> analysis -> unit = fun ff analysis ->
  let pp_diff ff (i, f) = Format.fprintf ff "(%i, %f)" i f in
  Format.fprintf ff "total_ref.bt_total = %i\n%!" analysis.total_ref.bt_total;
  Format.fprintf ff "total_ref.bt_cpp2v = %i\n%!" analysis.total_ref.bt_cpp2v;
  Format.fprintf ff "total_ref.bt_other = %i\n%!" analysis.total_ref.bt_other;
  Format.fprintf ff "total_new.bt_total = %i\n%!" analysis.total_new.bt_total;
  Format.fprintf ff "total_new.bt_cpp2v = %i\n%!" analysis.total_new.bt_cpp2v;
  Format.fprintf ff "total_new.bt_other = %i\n%!" analysis.total_new.bt_other;
  Format.fprintf ff "total_diff.bt_total = %a\n%!" pp_diff analysis.total_diff.bt_total;
  Format.fprintf ff "total_diff.bt_cpp2v = %a\n%!" pp_diff analysis.total_diff.bt_cpp2v;
  Format.fprintf ff "total_diff.bt_other = %a\n%!" pp_diff analysis.total_diff.bt_other;
  Format.fprintf ff "num_disappeared = %i\n%!" analysis.num_disappeared;
  Format.fprintf ff "total_disappeared = %a\n%!" pp_diff analysis.total_disappeared;
  Format.fprintf ff "num_appeared = %i\n%!" analysis.num_appeared;
  Format.fprintf ff "total_appeared = %a\n%!" pp_diff analysis.total_appeared;
  Format.fprintf ff "length per_file = %i\n%!" (List.length analysis.per_file)

let analyse : excluded:string list -> ref_data:string -> new_data:string list
    -> analysis = fun ~excluded ~ref_data ~new_data ->
  (* Read the data from the input files. *)
  let data = Data.get ~ref_data ~new_data in
  (* Only keep data from non-excluded folders. *)
  let data =
    let not_excluded file _ =
      let not_prefix prefix = not (String.starts_with ~prefix file) in
      List.for_all not_prefix excluded
    in
    M.filter not_excluded data
  in
  (* Gather appeared / disappeared files. *)
  let (appeared, total_appeared, disappeared, total_disappeared) =
    let gather file data (appeared, i_appeared, disappeared, i_disappeared) =
      match (data.Data.instr_ref, data.Data.instr) with
      | (Some(i), None   ) ->
          (appeared, i_appeared, S.add file disappeared, i_disappeared - i)
      | (None   , Some(i)) ->
          (S.add file appeared, i_appeared + i, disappeared, i_disappeared)
      | (_      , _      ) ->
          (appeared, i_appeared, disappeared, i_disappeared)
    in
    M.fold gather data (S.empty, 0, S.empty, 0)
  in
  let num_disappeared = S.cardinal disappeared in
  let num_appeared = S.cardinal appeared in
  (* Compute the performance diffs. *)
  let combined : (bool * (instr_count * instr_count * diff)) M.t =
    let make_diff i_ref i = (i_ref, i, make_diff i_ref i) in
    let filter _ data =
      match (data.Data.instr_ref, data.Data.instr) with
      (* We have data on both side. *)
      | (Some(i_ref), Some(i)) -> Some(true, make_diff i_ref i)
      (* We have data in the reference only, file disappeared. *)
      | (Some(i_ref), None   ) -> Some(false, make_diff i_ref i_ref)
      (* We have new data only, file appeared. *)
      | (None       , Some(i)) -> Some(false, make_diff i i)
      (* Unreachable case. *)
      | (None       , None   ) -> assert false
    in
    M.filter_map filter data
  in
  (* Computing the total. *)
  let (total_ref, full_ref, total_new, full_new) =
    let fn fname (b, (d1,d2,_)) (acc1,acc2,acc3,acc4) =
      match b with
      | false -> (acc1, bt_add fname acc2 d1, acc3, bt_add fname acc4 d2)
      | true  -> (bt_add fname acc1 d1, bt_add fname acc2 d1, bt_add fname acc3 d2, bt_add fname acc4 d2)
    in
    M.fold fn combined (bt_zero, bt_zero, bt_zero, bt_zero)
  in
  let total_diff = bt_make_diff total_ref total_new in
  (* Calculate percentage of missing instructions *)
  let total_disappeared = negate_diff (make_diff full_ref.bt_total (full_ref.bt_total - total_disappeared)) in
  let total_appeared = negate_diff (make_diff full_new.bt_total (full_new.bt_total - total_appeared)) in
  (* Sorting by instruction diff percentage. *)
  let combined = M.bindings combined in
  let cmp (_, (_, (_, _, d1))) (_, (_, (_, _, d2))) =
    compare (snd d1) (snd d2)
  in
  let per_file = List.sort cmp combined in
  (* Return the data. *)
  { total_ref; total_new; total_diff; num_disappeared; total_disappeared;
    num_appeared; total_appeared; per_file }

let default_color_threshold    = 0.5
let default_relevant_threshold = 0.1
let default_instr_threshold    = 0.5

let color_threshold    : float ref = ref default_color_threshold
let relevant_threshold : float ref = ref default_relevant_threshold
let instr_threshold    : float ref = ref default_instr_threshold
let show_everything    : bool  ref = ref false

let excluded = ref []

let add_excluded : string -> unit = fun dir ->
  excluded := dir :: !excluded

let debug_analysis = ref false

let color diff =
  if diff < -. !color_threshold then green "%+7.2f%%" else
  if diff > !color_threshold then red "%+7.2f%%" else
  "%+7.2f%%"

type output_format =
  | Markdown
  | Gitlab
  | Github
  | CSV

let output_format : output_format ref = ref Markdown
let diff_base_url : string option ref = ref None

let github_color diff =
  if not !use_colors then "%+7.2f%%" ^^ "" else
  if diff < -. !color_threshold then "$\\color{green}{%+7.2f\\\\%%}$" else
  if diff > !color_threshold then "$\\color{red}{%+7.2f\\\\%%}$" else
  "${%+7.2f\\\\%%}$"

let print_md_summary ?(mode : [`Github | `Gitlab] option = None) analysis =
  let {total_ref; total_new; total_diff; _} = analysis in
  let {num_disappeared=num_dis; total_disappeared=total_dis; _} = analysis in
  let {num_appeared=num_app; total_appeared=total_app; _} = analysis in
  let color = match mode with Some(`Github) -> github_color | _ -> color in
  (* Printing the totals. *)
  let print_summary infostring ?total_ref ?total_new total_diff =
    let pp_total ff io =
      match io with
      | None    -> Format.fprintf ff "       -"
      | Some(i) -> Format.fprintf ff "%8.1f" (float_of_int i /. 1000000000.0)
    in
    let d = float_of_int (fst total_diff) /. 1000000000.0 in
    info ("| " ^^ color (snd total_diff) ^^ " | %a | %a | %+8.1f | %s\n")
      (snd total_diff) pp_total total_ref pp_total total_new d infostring
  in
  let _ =
    let total_ref = total_ref.bt_total - fst total_dis in
    let total_new = total_new.bt_total + fst total_app in
    let total_diff = make_diff total_ref total_new in
    print_summary "total" ~total_ref ~total_new total_diff
  in
  (if num_dis > 0 then
      let disappeared_label = Printf.sprintf "├ disappeared files (%i)" num_dis in
      print_summary disappeared_label ~total_ref:(- fst total_dis) total_dis);
  (if num_app > 0 then
      let appeared_label = Printf.sprintf "├ newly appeared files (%i)" num_app in
      print_summary appeared_label ~total_new:(fst total_app) total_app);
  (if num_dis > 0 || num_app > 0 then
      print_summary "└ common files" ~total_new:total_new.bt_total ~total_ref:total_ref.bt_total total_diff.bt_total);
  (if total_ref.bt_cpp2v <> 0 && total_new.bt_cpp2v <> 0 then
      print_summary "├ translation units" ~total_new:total_new.bt_cpp2v ~total_ref:total_ref.bt_cpp2v total_diff.bt_cpp2v);
  print_summary "└ proofs and tests" ~total_new:total_new.bt_other ~total_ref:total_ref.bt_other total_diff.bt_other

let print_md_header () =
  info "| Relative | Master   | MR       | Change   | Filename\n";
  info "|---------:|---------:|---------:|---------:|----------\n"

let print_md_data ?(mode : [`Github | `Gitlab] option = None) analysis =
  let color = match mode with Some(`Github) -> github_color | _ -> color in
  print_md_header ();
  let add_url k =
    match !diff_base_url with
    | None -> k
    | Some(url) ->
        Printf.sprintf "[%s](%s/%s.html)" k url (Filename.chop_extension k)
  in
  let fn (k, (_, (n0, n1, (d, diff)))) =
    let instr_diff = float_of_int d /. 1000000000.0 in
    let relevant =
      abs_float diff >= !relevant_threshold &&
      abs_float instr_diff >= !instr_threshold
    in
    if !show_everything || relevant then
      let n0 = float_of_int n0 /. 1000000000.0 in
      let n1 = float_of_int n1 /. 1000000000.0 in
      info ("| " ^^ color diff ^^ " | %8.1f | %8.1f | %+8.1f | %s\n")
        diff n0 n1 instr_diff (add_url k)
  in
  List.iter fn analysis.per_file;
  if mode != None then
    info "|          |          |          |          |          \n";
  print_md_summary ~mode analysis

let print_gitlab_or_github_data ~mode analysis =
  let fn url =  info "\n[Full performance report](%s/index.html)\n\n" url in
  Option.iter fn !diff_base_url;
  print_md_header ();
  print_md_summary ~mode:(Some(mode)) analysis;
  info "\n<details><summary>Full Results</summary>\n\n";
  print_md_data ~mode:(Some(mode)) analysis;
  info "\n</details>\n"

let print_csv_data analysis =
  let {total_ref; total_new; total_diff; per_file; _} = analysis in
  info "Relative (%%),Master (instr),MR (instr),Change (instr),Filename\n";
  let fn (k, (_, (n0, n1, (d, diff)))) =
    info "%f,%i,%i,%i,%s\n" diff n0 n1 d k
  in
  List.iter fn per_file;
  (* Printing the total. *)
  info "%f,%i,%i,%i,*\n" (snd total_diff.bt_total) total_ref.bt_total total_new.bt_total (fst total_diff.bt_total)

let analyse : ref_data:string -> new_data:string list -> unit =
    fun ~ref_data ~new_data ->
  let analysis = analyse ~excluded:!excluded ~ref_data ~new_data in
  if !debug_analysis then
    Format.eprintf "### DEBUG ###\n%a#############\n%!" pp_analysis analysis;
  match !output_format with
  | Markdown -> print_md_data ~mode:None analysis
  | Gitlab   -> print_gitlab_or_github_data ~mode:`Gitlab analysis
  | Github   -> print_gitlab_or_github_data ~mode:`Github analysis
  | CSV      -> print_csv_data analysis

let usage : string -> bool -> 'a = fun prog_name error ->
  if error then panic "Usage: %s BASE.csv JOB_1.csv .. JOB_n.csv" prog_name;
  einfo "Usage: %s BASE.csv JOB_1.csv .. JOB_n.csv\n\n" prog_name;
  einfo "Output the total and per-file differences in instruction counts \
         between the base pipeline (given in BASE.csv) and multiple job \
         pipeline (given in JOB_i.csv, listed in chronological order since \
         in case of overlap the last file wins).\n\n";
  einfo "When performance data is only available in the base data, or only \
         available in the job data, then the performance is assumed to be \
         unchanged on that file (it is contained in the total instruction \
         count).\n";
  einfo "Supported arguments:\n";
  einfo "  --help, -h                 \tShow this help message.\n";
  einfo "  --no-colors                \tDo not output any colors.\n";
  einfo "  --show-all                 \tInclude all data in the output.\n";
  einfo "  --color-threshold FLOAT    \tMinimum difference shown in color \
                                        (in percent, default %1.1f).\n"
                                        default_color_threshold;
  einfo "  --threshold FLOAT          \tMinimum difference considered \
                                        significant (in percent, default = %1.1f\
                                        ).\n" default_relevant_threshold;
  einfo "  --instr-threshold FLOAT    \tMinimum difference considered \
                                        significant (in billions of \
                                        instructons, default %1.1f).\n"
                                        default_instr_threshold;
  einfo "  --csv                      \tPrint the full raw data in CSV.\n";
  einfo "  --markdown                 \tMarkdown output.\n";
  einfo "  --gitlab                   \tMarkdown output compiled into a \
                                        small summary and a <details> section.\n";
  einfo "  --github                   \tMarkdown output compiled into a \
                                        small summary and a <details> section.\n";
  einfo "  --diff-base-url URL        \tSpecify the base URL for diffs.\n";
  einfo "  --exclude DIR              \tExcludes files whose path starts \
                                        with DIR.\n";
  einfo "  --debug-analysis           \tPrint the output of the analysis phase.\n";
  exit 0

let main () =
  let (prog_name, args) =
    let args = List.tl (Array.to_list Sys.argv) in
    (Sys.argv.(0), args)
  in
  let rec parse_args files args =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    let parse_float opt s =
      try float_of_string s with Failure(_) ->
        panic "Invalid parameter for argument \"%s\" (found \"%s\")." opt s
    in
    match args with
    | ("--help" | "-h")             :: _                     ->
        usage prog_name false
    | "--no-colors"                 :: args                  ->
        use_colors := false;
        parse_args files args
    | "--show-all"                  :: args                  ->
        show_everything := true;
        parse_args files args
    | "--color-threshold" as a      :: []                    ->
        panic "Command line argument \"%s\" expects a float." a;
    | "--color-threshold" as a :: f :: args                  ->
        color_threshold := parse_float a f;
        parse_args files args
    | "--threshold"       as a      :: []                    ->
        panic "Command line argument \"%s\" expects a float." a;
    | "--threshold"       as a :: f :: args                  ->
        relevant_threshold := parse_float a f;
        parse_args files args
    | "--instr-threshold" as a      :: []                    ->
        panic "Command line argument \"%s\" expects an int." a;
    | "--instr-threshold" as a :: f :: args                  ->
        instr_threshold := parse_float a f;
        parse_args files args
    | "--csv"                       :: args                  ->
        output_format := CSV;
        parse_args files args
    | "--markdown"                  :: args                  ->
        output_format := Markdown;
        parse_args files args
    | "--gitlab"                    :: args                  ->
        output_format := Gitlab;
        parse_args files args
    | "--github"                    :: args                  ->
        output_format := Github;
        parse_args files args
    | "--diff-base-url" :: url      :: args                  ->
        diff_base_url := Some(url);
        parse_args files args
    | "--exclude" :: dir            :: args                  ->
        add_excluded dir;
        parse_args files args
    | "--debug-analysis"            :: args                  ->
        debug_analysis := true;
        parse_args files args
    | "--assume-missing-unchanged"  :: args                  ->
        (* TODO remove when possible. *)
        parse_args files args
    | arg                           :: _ when is_flag arg    ->
        panic "Invalid command line argument \"%s\"." arg;
    | file                          :: args                  ->
        if try Sys.is_directory file with Sys_error(_) -> false then
          panic "File expected, [%s] is a directory." file;
        if not (Sys.file_exists file) then
          panic "No such file or directory [%s]." file;
        parse_args (file :: files) args
    | []                                                     ->
        List.rev files
  in
  let files = parse_args [] args in
  match files with
  | ref_data :: (_ :: _ as new_data) -> analyse ~ref_data ~new_data
  | _                                ->
      let n = List.length files in
      panic "at least 2 file paths expected on the command line (%i given)." n

let _ =
  try main () with
  | Sys_error(msg) -> panic "%s" msg
  | e              -> panic "Uncaught exception: %s." (Printexc.to_string e)
