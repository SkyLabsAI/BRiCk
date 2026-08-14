  $ . ../../setup-cpp2v.sh
  $ probe=../../../build-dune-tests/cpp2v-declaration-builder-probe
  $ "$probe" fixture.cpp Built17 -- -std=c++17 > built17.v
  $ "$probe" fixture.cpp Built20 -- -std=c++20 > built20.v
  $ rocq c $ROCQC_ARGS built17.v
  $ rocq c $ROCQC_ARGS built20.v

The owned declaration records are stable across the supported language modes.

  $ cat > versions.v <<'EOF'
  > Require Import built17 built20.
  > Example ordinary_objects_stable :
  >   Built17.ordinary_objects = Built20.ordinary_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example ordinary_globals_stable :
  >   Built17.ordinary_globals = Built20.ordinary_globals.
  > Proof. vm_compute. reflexivity. Qed.
  > Example duplicate_roots_stable :
  >   Built17.duplicate_globals = Built20.duplicate_globals.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_duplicate_roots_stable :
  >   Built17.duplicate_template_globals =
  >   Built20.duplicate_template_globals.
  > Proof. vm_compute. reflexivity. Qed.
  > Example implicit_fallbacks_stable :
  >   Built17.fallback_objects = Built20.fallback_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example exception_holder_objects_stable :
  >   Built17.exception_holder_objects = Built20.exception_holder_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_objects_stable :
  >   Built17.template_objects = Built20.template_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_globals_stable :
  >   Built17.template_globals = Built20.template_globals.
  > Proof. vm_compute. reflexivity. Qed.
  > Example namespace_alias_events_stable :
  >   Built17.namespace_alias_events = Built20.namespace_alias_events /\
  >   Built17.production_namespace_alias_events =
  >     Built20.production_namespace_alias_events.
  > Proof. vm_compute. auto. Qed.
  > Example static_assertion_events_stable :
  >   Built17.static_assertion_events = Built20.static_assertion_events.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_alias_events_stable :
  >   Built17.template_alias_events = Built20.template_alias_events.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_instance_events_stable :
  >   Built17.template_instance_events = Built20.template_instance_events.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_enum_suppression_stable :
  >   Built17.production_template_enum_count = 1 /\
  >   Built20.production_template_enum_count = 1 /\
  >   Built17.production_template_enum_constant_count = 0 /\
  >   Built20.production_template_enum_constant_count = 0.
  > Proof. vm_compute. auto. Qed.
  > Example production_seeds_stable :
  >   Built17.production_seed_count = 28 /\
  >   Built20.production_seed_count = 28.
  > Proof. vm_compute. auto. Qed.
  > EOF
  $ rocq c $ROCQC_ARGS versions.v

Generate the production module independently from the focused probe. Lookup in its folded maps
must equal each final owned root value, including eager static-method and
template-parameter helper reduction.

  $ cpp2v -o production17.v --templates production17_templates.v fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS production17_templates.v
  $ rocq c $ROCQC_ARGS production17.v
  $ cat > parity17.v <<'EOF'
  > Require Import skylabs.prelude.base.
  > Require Import skylabs.lang.cpp.parser.
  > Require Import skylabs.lang.cpp.mparser.
  > Require Import production17 built17.
  > Import skylabs.lang.cpp.syntax.
  > Example ordinary_objects_match :
  >   List.map (fun '(name, _) => (production17.static__source).(symbols) !! name)
  >     Built17.ordinary_objects =
  >   List.map (fun '(_, value) => Some value) Built17.ordinary_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example ordinary_globals_match :
  >   List.map (fun '(name, _) => (production17.static__source).(types) !! name)
  >     Built17.ordinary_globals =
  >   List.map (fun '(_, value) => Some value) Built17.ordinary_globals.
  > Proof. vm_compute. reflexivity. Qed.
  > Definition duplicate_default : name * GlobDecl :=
  >   (Nunsupported "missing", Gunsupported "missing").
  > Definition duplicate_first :=
  >   List.hd duplicate_default Built17.duplicate_globals.
  > Definition duplicate_last :=
  >   List.last Built17.duplicate_globals duplicate_default.
  > Example duplicate_roots_are_compatible_unequal :
  >   duplicate_first.1 = duplicate_last.1 /\
  >   duplicate_first.2 <> duplicate_last.2.
  > Proof. vm_compute. split; congruence. Qed.
  > Example duplicate_fold_selects_definition :
  >   (production17.static__source).(types) !! duplicate_last.1 =
  >   Some duplicate_last.2.
  > Proof. vm_compute. reflexivity. Qed.
  > Definition template_duplicate_default :=
  >   (Nunsupported "missing", Template nil (Gunsupported "missing")).
  > Definition template_duplicate_first :=
  >   List.hd template_duplicate_default
  >     Built17.duplicate_template_globals.
  > Definition template_duplicate_last :=
  >   List.last Built17.duplicate_template_globals
  >     template_duplicate_default.
  > Example template_duplicate_roots_are_unequal :
  >   template_duplicate_first.1 = template_duplicate_last.1 /\
  >   template_duplicate_first.2 <> template_duplicate_last.2.
  > Proof. vm_compute. split; congruence. Qed.
  > Example template_overwrite_selects_definition :
  >   (production17.source).(mtypes) !! template_duplicate_last.1 =
  >   Some template_duplicate_last.2.
  > Proof. vm_compute. reflexivity. Qed.
  > Definition fallback_name : name := "FallbackOnly"%cpp_name.
  > Definition fallback_expected :=
  >   (skylabs.lang.cpp.parser.translation_unit.list_decls
  >      [Oimplicit_default_ctor fallback_name;
  >       Oimplicit_copy_ctor fallback_name true;
  >       Oimplicit_move_ctor fallback_name false;
  >       Oimplicit_copy_assign fallback_name true;
  >       Oimplicit_move_assign fallback_name;
  >       Oimplicit_dtor fallback_name]
  >      abi.abi_default).1.
  > Example implicit_fallbacks_match :
  >   List.map (fun '(name, _) => fallback_expected.(symbols) !! name)
  >     Built17.fallback_objects =
  >   List.map (fun '(_, value) => Some value) Built17.fallback_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example exception_holder_objects_match :
  >   List.map (fun '(name, _) => (production17.static__source).(symbols) !! name)
  >     Built17.exception_holder_objects =
  >   List.map (fun '(_, value) => Some value)
  >     Built17.exception_holder_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example exception_holder_specs_resolved :
  >   List.map
  >     (fun '(_, value) =>
  >        skylabs.lang.cpp.syntax.translation_unit.can_throw value)
  >     Built17.exception_holder_objects = [exception_spec.NoThrow].
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_objects_match :
  >   List.map (fun '(name, _) => (production17.source).(msymbols) !! name)
  >     Built17.template_objects =
  >   List.map (fun '(_, value) => Some value) Built17.template_objects.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_globals_match :
  >   List.map (fun '(name, _) => (production17.source).(mtypes) !! name)
  >     Built17.template_globals =
  >   List.map (fun '(_, value) => Some value) Built17.template_globals.
  > Proof. vm_compute. reflexivity. Qed.
  > Example templated_enum_constant_is_absent :
  >   (production17.source).(mtypes) !!
  >     Built17.suppressed_template_enum_constant_name = None.
  > Proof. vm_compute. reflexivity. Qed.
  > Definition expected_static_events :=
  >   (skylabs.lang.cpp.parser.translation_unit.list_decls
  >      ((List.map
  >          (fun '(from, to) =>
  >             match from with
  >             | Some from => Dusing_namespace from to
  >             | None => Dglobal_using_namespace to
  >             end)
  >          Built17.production_namespace_alias_events) ++
  >       (List.map
  >          (fun assertion =>
  >             Dstatic_assert (Some assertion.(sa_message))
  >               assertion.(sa_condition))
  >          Built17.static_assertion_events))
  >      abi.abi_default).1.
  > Example namespace_aliases_match :
  >   (production17.static__source).(namespace_aliases) =
  >   expected_static_events.(namespace_aliases).
  > Proof. vm_compute. reflexivity. Qed.
  > Example static_assertions_match :
  >   (production17.static__source).(asserts) = expected_static_events.(asserts).
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_aliases_match :
  >   List.map (fun '(name, _) => (production17.source).(maliases) !! name)
  >     Built17.template_alias_events =
  >   List.map (fun '(_, value) => Some value)
  >     Built17.template_alias_events.
  > Proof. vm_compute. reflexivity. Qed.
  > Example template_instances_match :
  >   List.map (fun '(name, _) => (production17.source).(minstances) !! name)
  >     Built17.template_instance_events =
  >   List.map (fun '(_, value) => Some value)
  >     Built17.template_instance_events.
  > Proof. vm_compute. reflexivity. Qed.
  > EOF
  $ rocq c $ROCQC_ARGS parity17.v

  $ cpp2v -o production20.v --templates production20_templates.v fixture.cpp -- -std=c++20
  $ rocq c $ROCQC_ARGS production20_templates.v
  $ rocq c $ROCQC_ARGS production20.v
  $ sed 's/production17/production20/g; s/built17/built20/g; s/Built17/Built20/g' parity17.v > parity20.v
  $ rocq c $ROCQC_ARGS parity20.v
