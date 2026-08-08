Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.source_location.

#[local] Open Scope pstring_scope.

#[local] Definition source_files : list source_file := [].
#[local] Definition source_origins : list source_origin := [].
#[local] Definition root_name : name := Nglobal (Nid "duplicate").
#[local] Definition located_root_events :
    list Construction.located_root_event :=
  [ Construction.LESymbol root_name
      (Ovar (Tnum int_rank.Iint Signed) global_init.NoInit) (LocNode [] [])
  ; Construction.LESymbol root_name
      (Ovar Tbool global_init.NoInit) (LocNode [] [])
  ].

Definition source_locations : source_map.
Proof.
  Construction.build_source_map_or_fail
    source_files source_origins located_root_events.
Defined.
