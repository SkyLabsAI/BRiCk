(*
 * Copyright (C) 2025-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

module String = Stdlib.String

include Stdlib.Filename

let concat : string -> string -> string = fun f1 f2 ->
  if f1 = current_dir_name then f2 else
  if f2 = current_dir_name then f1 else
  concat f1 f2

let decompose : string -> string * string * string = fun file ->
  let ext = extension file in
  let ext_len = String.length ext in
  let ext = if ext_len = 0 then ext else String.sub ext 1 (ext_len - 1) in
  (dirname file, remove_extension (basename file), ext)

let is_clean_relative : string -> bool = fun file ->
  is_relative file &&
  let ok s = s <> current_dir_name && s <> parent_dir_name in
  List.for_all ok (String.split_on_char '/' file)
