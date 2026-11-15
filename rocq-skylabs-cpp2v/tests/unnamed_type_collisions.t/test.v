Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.

Require Import test_cpp (source).

(* [test_cpp] compiling at all means that no two declarations clash: the
   generated translation unit is checked for duplicates. *)

Definition size_of (n : name) : option N :=
  match source.(types) !! n with
  | Some (Gstruct s) => Some s.(s_size)
  | _ => None
  end.

Definition first_field (n : name) : option field_name.t :=
  match source.(types) !! n with
  | Some (Gstruct s) => mem_name <$> head s.(s_fields)
  | _ => None
  end.

Definition enum_value (n : name) : option Z :=
  match source.(types) !! n with
  | Some (Gconstant _ (Some (Ecast _ (Eint z _)))) => Some z
  | _ => None
  end.

(* [Nrecord_by_field]: only the first record is named after its field. *)
Example H_first : size_of "H::.a"%cpp_name = Some 8%N := ltac:(vm_compute; reflexivity).
Example H_second : size_of "H::@1"%cpp_name = Some 24%N := ltac:(vm_compute; reflexivity).

(* [Nby_first_decl]: only the first record is named after its variable. *)
Example records_first : first_field "records()::@x"%cpp_name = Some (Nid "a") := ltac:(vm_compute; reflexivity).
Example records_second : first_field "records()::@1"%cpp_name = Some (Nid "b") := ltac:(vm_compute; reflexivity).

(* [Nenum_by_enumerator]: each enumerator is found under its own enumeration,
   without a discriminator, as [Eenum_const] references print it. *)
Example enums_first : enum_value "enums()::.A::A"%cpp_name = Some 1%Z := ltac:(vm_compute; reflexivity).
Example enums_second : enum_value "enums()::@1::A"%cpp_name = Some 0%Z := ltac:(vm_compute; reflexivity).

(* [Nrecord_by_field] and [Nenum_by_enumerator] share [Nfirst_child]. *)
Example mixed_record : size_of "mixed()::.K"%cpp_name = Some 4%N := ltac:(vm_compute; reflexivity).
Example mixed_enum : enum_value "mixed()::@1::K"%cpp_name = Some 0%Z := ltac:(vm_compute; reflexivity).

(* Typedef names for anonymous records get the usual local discriminator. *)
Example typedefs_first : size_of "typedefs()::S"%cpp_name = Some 4%N := ltac:(vm_compute; reflexivity).
Example typedefs_second :
  size_of (Nscoped "typedefs()"%cpp_name (Nid "S'0"%pstring)) = Some 8%N := ltac:(vm_compute; reflexivity).
