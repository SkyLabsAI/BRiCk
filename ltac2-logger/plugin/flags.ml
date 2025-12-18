open Stdlib_extra.Extra
open Logger_lib
open Rocq_extra.Extra

(** Flag identifier. *)
module FlagId = struct
  (** Representation of a flag identifier: a module path and in identifier. *)
  type t = Names.ModPath.t * Names.Id.t

  let pp : t Format.pp = fun ff (mp, id) ->
    Format.pp_print_string ff (Names.ModPath.to_string mp);
    Format.pp_print_char ff '.';
    Format.pp_print_string ff (Names.Id.to_string id)

  let to_string : t -> string = fun (mp, id) ->
    let mp = Names.ModPath.to_string mp in
    let id = Names.Id.to_string id in
    Format.sprintf "%s.%s" mp id

  (** [make id] builds a flag identifier named [id] in the current module path
      at the point where the function is called. *)
  let make : Names.Id.t -> t = fun id ->
    (Lib.current_mp (), id)

  (** [equal f1 f2] tests whether [f1] and [f2] are equal. *)
  let equal : t -> t -> bool = fun (mp1, id1) (mp2, id2) ->
    Names.Id.equal id1 id2 && Names.ModPath.equal mp1 mp2

  (** [hash f] computes a hash for [f], which we will use as key to access the
      corresponding flag's data. We will enforce that the set of flags we work
      with have pairwise distinct hashes to forbid collisions. *)
  let hash : t -> int = fun (mp, id) ->
    Names.ModPath.hash mp lxor Names.Id.hash id
end

module IMap = Map.Make(Int)

(** Type representing the logging level for a flag. *)
type level = int

(** Data associated to a flag. *)
type flag_data = {
  id  : FlagId.t; (** Flag identifier.        *)
  dev : bool;     (** Is this a "dev" flag?   *)
}

module State : sig
  (** Representation of the log flag state. *)
  type t = flag_data IMap.t

  (** [get ()] returns the current state. *)
  val get : unit -> t

  (** [set s] sets the current state to [s]. *)
  val set : t -> unit
end = struct
  type t = flag_data IMap.t

  let state =
    Summary.ref ~name:"log_flags_state" IMap.empty

  let declare_state : t -> Libobject.obj =
    let open Libobject in
    let cache_function s =
      let merge _ data1 data2 =
        assert (FlagId.equal data1.id data2.id);
        assert (data1.dev = data2.dev);
        Some(data1)
      in
      state := IMap.union merge !state s
    in
    let load_function _ = cache_function in
    let classify_function _ = Keep in
    let default = default_object "LOG_FLAGS_STATE" in
    declare_object 
      {default with cache_function; load_function; classify_function}

  let get () = !state
  let set s = Lib.add_leaf (declare_state s)
end

(** A flag is represented by its hash at the FFI boundary. *)
type flag = int

let repr = Ltac2_plugin.Tac2ffi.int

module Levels = struct
  type map = level IMap.t

  let to_string : map -> string = fun levels ->
    let flag_map = State.get () in
    let b = Buffer.create 1024 in
    let add_data key {id=(mp, id); _} =
      let lvl = try IMap.find key levels with Not_found -> 0 in 
      match lvl with
      | 0 -> ()
      | _ ->
          if not (Buffer.is_empty b) then Buffer.add_char b ',';
          Buffer.add_string b (Names.ModPath.to_string mp);
          Buffer.add_char b '.';
          Buffer.add_string b (Names.Id.to_string id);
          Buffer.add_char b '=';
          Buffer.add_string b (string_of_int lvl)
    in
    IMap.iter add_data flag_map;
    Buffer.contents b

  let of_string : string -> map = fun fields ->
    (* Get the separate fields (separated by a comma, trim spaces). *)
    let fields =
      match List.map String.trim (String.split_on_char ',' fields) with
      | [""]   -> []
      | fields -> fields
    in
    (* Separate fields into a LHS and a RHS. *)
    let fields =
      let split field =
        match List.map String.trim (String.split_on_char '=' field) with
        | [""; _    ] -> failwith "Missing flag name in %S." field
        | [_ ; ""   ] -> failwith "Missing flag level in %S." field
        | [id; level] ->
            let level =
              let level =
                try int_of_string level with Failure(_) ->
                failwith "Parse error in %S (value not not an integer)." field
              in
              if level >= 0 then level else
                failwith "Parse error in %S (%i < 0)." field level
            in
            (id, level)
        | _           ->
            failwith "Parse error in %S: expected [flag=level]." field
      in
      List.map split fields
    in
    (* Interpret the LHS of every field. *)
    let flag_map = State.get () in
    let fields =
      let module SMap = Map.Make(String) in
      let exception Ambiguous of FlagId.t list in
      let find_key : string -> int =
        let m =
          let fn k {id; _} m =
            let m = SMap.add (FlagId.to_string id) [(id, k)] m in
            let short = Names.Id.to_string (snd id) in
            let ids =
              match SMap.find_opt short m with
              | Some(ids) -> ids @ [(id, k)]
              | None      -> [(id, k)]
            in
            SMap.add short ids m
          in
          IMap.fold fn flag_map SMap.empty
        in
        let find s =
          match SMap.find s m with
          | []       -> assert false
          | [(_, k)] -> k
          | ids      -> raise (Ambiguous(List.map fst ids))
        in find
      in
      let interp id =
        match id with
        | "*" | "@all"     -> `All
        | "_" | "@default" -> `Def
        | _                ->
        try `Key(find_key id) with
        | Not_found      -> failwith "Unknown flag %S." id
        | Ambiguous(ids) ->
            let pp_sep ff () = Format.pp_print_string ff ", " in
            failwith "Flag %S is ambiguous, it could stand for either of %a."
              id (Format.pp_print_list ~pp_sep FlagId.pp) ids
      in
      List.map (fun (id, level) -> (interp id, level)) fields
    in
    (* Set the levels. *)
    let get_level k flag =
      let interp cur_lvl (filter, lvl) =
        match filter with
        | `All                   -> lvl
        | `Def when not flag.dev -> lvl
        | `Key(i) when i = k     -> lvl
        | _                      -> cur_lvl
      in
      List.fold_left interp 0 fields
    in
    IMap.mapi get_level flag_map

  let get_map : unit -> map =
    let getter =
      Goptions.declare_interpreted_string_option_and_ref
        ~key:["BR";"Debug"] ~value:IMap.empty of_string to_string ()
    in
    getter.Goptions.get
end

let get_level : flag -> level = fun key ->
  try IMap.find key (Levels.get_map ()) with Not_found -> 0

let max_level : unit -> level = fun _ ->
  IMap.fold (fun _ lvl acc -> max acc lvl) (Levels.get_map ()) 0

let enabled : flag -> level -> bool = fun key level ->
  level <= get_level key

let get_name : flag -> string = fun key ->
  let flag_map = State.get () in
  let flag = try IMap.find key flag_map with Not_found -> assert false in
  Names.Id.to_string (snd flag.id)

let log_level : level -> Logger.Metadata.t =
  Logger.Metadata.make_int Fun.id "level"

(* FIXME: we only print the ident, could be ambiguous. *)
let log_flag : flag -> Logger.Metadata.t =
  Logger.Metadata.make_string get_name "flag"

let define_flag_value : string -> int -> unit = fun id hash ->
  let open Ltac2_plugin in
  let tac_name_str = "log_flag_" ^ id in
  let tac_name =
    CAst.make (Names.Name.mk_name (Names.Id.of_string tac_name_str))
  in
  let hash_expr = CAst.make Tac2expr.(CTacAtm(AtmInt(hash))) in
  Tac2entries.register_ltac false [(tac_name, hash_expr)];
  Msg.info "Ltac2 value \"%s\" is defined.\n%!" tac_name_str

let define_notation : with_level:bool -> string -> int -> unit =
    fun ~with_level id hash ->
  let open Ltac2_plugin in
  let sexpr_str s = Tac2expr.SexprStr(CAst.make s) in
  let sexpr_int i = Tac2expr.SexprInt(CAst.make i) in
  let sexpr_rec id args =
    let id = CAst.make (Some(Names.Id.of_string id)) in
    let dummy_loc = Loc.make_loc (0, 0) in
    Tac2expr.SexprRec(dummy_loc, id, args)
  in
  let tokens =
    let tokens = ref [] in
    let add_token tok = tokens := !tokens @ [tok] in
    add_token (sexpr_str "log[");
    add_token (sexpr_str id);
    if with_level then
      add_token (sexpr_str ",");
    if with_level then
      add_token (sexpr_rec "lvl" [sexpr_rec "tactic" [sexpr_int 0]]);
    add_token (sexpr_str "]");
    add_token (sexpr_rec "fmt" [sexpr_rec "format" []]);
    !tokens
  in
  let log_msg =
    let mp =
      let dp = ["skylabs"; "ltac2"; "logger"; "logger"] in
      let dp = List.rev_map Names.Id.of_string dp in
      let mp = Names.ModPath.MPfile(Names.DirPath.make dp) in
      Names.ModPath.MPdot(mp, Names.Label.make "Log")
    in
    let log = Names.KerName.make mp (Names.Label.make "log_msg") in
    CAst.make Tac2expr.(CTacRef(AbsKn(TacConstant(log))))
  in
  let body =
    let var id =
      let id = Libnames.qualid_of_string id in
      CAst.make Tac2expr.(CTacRef(RelId(id)))
    in
    let int_expr i = CAst.make Tac2expr.(CTacAtm(AtmInt(i))) in
    let args =
      [ int_expr hash
      ; (if with_level then var "lvl" else int_expr 1)
      ; var "fmt" ]
    in
    CAst.make Tac2expr.(CTacApp(log_msg, args))
  in
  let notation = Tac2entries.register_notation [] tokens None body in
  Tac2entries.register_notation_interpretation notation;
  Msg.info "Ltac2 notation \"log[%s%s] <format>\" is defined.\n%!"
    id (if with_level then ",<level>" else "")

let declare_ltac2_log_flag : Names.Id.t -> bool -> unit = fun id dev ->
  let id_str = Names.Id.to_string id in
  let id = FlagId.make id in
  (* Check that no flags was defined with the same name. *)
  let flag_map = State.get () in
  if IMap.exists (fun _ flag -> FlagId.equal id flag.id) flag_map then
    failwith "The flag already exists.";
  (* Check that no flags was defined with the same hash. *)
  let hash = FlagId.hash id in
  if IMap.mem hash flag_map then
    failwith "Hash conflict for a flag.";
  (* Register the flag. *)
  let flag_map = IMap.add hash {id; dev} flag_map in
  State.set flag_map;
  (* Define an Ltac2 value for the flag (its hash). *)
  define_flag_value id_str hash;
  (* Define Ltac2 notations for logging with the flag. *)
  define_notation ~with_level:true  id_str hash;
  define_notation ~with_level:false id_str hash

let print_ltac2_log_flags : unit -> unit = fun _ ->
  let flag_map = State.get () in
  let print_flag_descr key {id; dev} =
    let lvl = try IMap.find key (Levels.get_map ()) with Not_found -> 0 in
    let grp = if dev then '*' else '_' in
    Msg.info "key=0x%x group=%c level=%i name=%a\n%!" key grp lvl FlagId.pp id
  in
  IMap.iter print_flag_descr flag_map
