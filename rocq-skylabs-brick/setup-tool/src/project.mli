open Extra

(** Project configuration read / written to file ["br-project.toml"], which is
    also used to identify the root of the project on the file system. *)
type br_project = {
  brp_coq_dirpath    : Coq_path.t;
  (** Main Coq directory path for the project. *)
  brp_coq_package    : string;
  (** Main opam package name for the project. *)
  brp_coq_theories   : string list;
  (** Coq theories to include in generate theories. *)
  brp_clang_includes : Filepath.t list;
  (** Clang included directories (for ["#include<...>"]). *)
  brp_clang_flags    : string list;
  (** Other clang flags, excluding ["-I"]. *)
  brp_proj_ignored   : Filepath.t list;
  (** C++ source files, or whole directories to ignore. *)
}

(** Option configuration mode. *)
type config_mode =
  | Extend
  (** Extend the default. *)
  | Override
  (** Override the option (ignoring the default). *)

(** Local configuration read / written to a ["br-config.toml"] file. It can be
    used to set options in a specific subtree of the source tree. *)
type br_config = {
  brc_coq_dirpath    : Coq_path.t option;
  (** Optional Coq directory path for files under the same directory. *)
  brc_coq_package    : string option;
  (** Optional opam package name for for files under the same directory. *)
  brc_coq_theories   : (config_mode * string list);
  (** Coq theories to include in generate theories. *)
  brc_clang_includes : config_mode * Filepath.t list;
  (** Clang included directories (for ["#include<...>"]). *)
  brc_clang_flags    : config_mode * string list;
  (** Other clang flags, excluding ["-I"]. *)
  brc_proj_ignored   : Filepath.t list;
  (** C++ source files, or whole directories to ignore. *)
}

(** [read_br_project file] reads a project configuration from the given [file]
    (in Toml format). In case of failure while reading or parsing the file, an
    error message is printed, and the program fails with exit code [1]. *)
val read_br_project : Filepath.t -> br_project

(** [write_br_project file config] writes the given [config] to the [file]. In
    case of failure while writing the file, an error message is printed before
    the failure of the program with exit code [1]. *)
val write_br_project : Filepath.t -> br_project -> unit

(** [read_br_config] is similar to [read_br_project], but reads a local config
    file instead of a project config file. *)
val read_br_config : Filepath.t -> br_config

(** [write_br_config] is similar to [write_br_project], but applies to a local
    config file instead of a project config file. *)
val write_br_config : Filepath.t -> br_config -> unit

(** Name of the project configuration file (identifying the project root). *)
val project_file_name : string

(** Name of the local configuration files. *)
val config_file_name : string

(** [locate_root ()] identifies the project root by finding a parent directory
    (of the current working directory) that contains file [project_file_name].
    If no project root can be located, the function returns [None]. Otherwise,
    it returns [Some(rootpath, rel)], where [rootpath] is the absolute path to
    the workspace root, and [rel] is a relative path from the project root, to
    the current working directory. *)
val locate_root : unit -> (Filepath.t * Filepath.t) option

(** [move_to_root ()] identifies the project root by calling [locate_root ()],
    and aborts the whole program in case of failure. The function then changes
    the current working directory to be the project root, and returns the path
    to the previous working directory returned by [locate_root]. *)
val move_to_root : unit -> Filepath.t

(** Configuration of the generator for a given C++ source file. *)
type config = {
  coq_dirpath    : Coq_path.t;
  (** Coq directory path for the generated Coq theory. *)
  coq_package    : string;
  (** Opam package for the generated theory. *)
  coq_theories   : string list;
  (** Coq theories to include in the generate theory. *)
  clang_includes : Filepath.t list;
  (** Clang included directories (relative to source file's directory). *)
  clang_flags    : string list;
  (** Clang flags for the source file. *)
  proj_ignored   : Filepath.t list;
  (** Known ignored paths (relative to the project root). *)
}

(** [discover ()] gives a list of pairs of C++ source file paths, and attached
    configurations. The function takes into account the project configuration,
    and returns an entry for all C/C++ source files not explicitly ignored. In
    case of failure, the program is aborted with an error message. *)
val discover : unit -> (Filepath.t * config) list
