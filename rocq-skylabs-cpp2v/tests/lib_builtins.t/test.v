Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax skylabs.lang.cpp.semantics.

Require nodecl_17_cpp decl_cpp.

(* The [memcpy] that cpp2v declares is below [<cstring>]'s in [sub_module]:
   it has no body, so its parameter names do not matter. *)
Example memcpy_le :
  match nodecl_17_cpp.source.(symbols) !! Nglobal (Nid "memcpy"),
        decl_cpp.source.(symbols) !! Nglobal (Nid "memcpy") with
  | Some a, Some b => ObjValue_le a b
  | _, _ => false
  end = true := ltac:(vm_compute; reflexivity).
