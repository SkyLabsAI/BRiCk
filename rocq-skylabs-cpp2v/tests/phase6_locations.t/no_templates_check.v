Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import no_templates_locations.

Example template_symbol_locations_are_empty :
    TM.elements source_locations.(declarations).(msymbol_locations) = [].
Proof. vm_compute. reflexivity. Qed.

Example template_type_locations_are_empty :
    TM.elements source_locations.(declarations).(mtype_locations) = [].
Proof. vm_compute. reflexivity. Qed.
