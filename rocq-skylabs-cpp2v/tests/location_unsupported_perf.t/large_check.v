Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import large_17_cpp_locations.

#[local] Open Scope pstring_scope.

Definition last_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "large_15"
        [Tnum int_rank.Iint Signed])).

Definition first_line (result : lookup_error + list source_origin) : option PrimInt63.int :=
  match result with
  | inr (origin :: _) =>
      match origin.(spelling_range) with
      | Some range =>
          match range.(range_begin) with
          | Some point => Some point.(point_line)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Example large_tu_deep_lookup_reduces :
    first_line
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        last_root [0; 2; 0; 0; 0; 1]) = Some 17%uint63.
Proof. vm_compute. reflexivity. Qed.
