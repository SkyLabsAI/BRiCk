  $ . ../../setup-cpp2v.sh

The isolated name probe renders explicit real BRiCk terms. Repeating it proves
deterministic node/source construction; the final line covers the first
function-name form migrated by Phase 4A.2.

  $ probe=../../../build-dune-tests/cpp2v-name-builder-probe
  $ "$probe" fixture.cpp -- -std=c++17 > first.out
  fixture.cpp:21:3: warning: declaration does not declare anything [-Wmissing-declarations]
     21 |   struct {};
        |   ^
  $ cat first.out
  (Nglobal (Nid "global_value"))
  (Nglobal (Nid "scope"))
  (Nscoped (Nglobal (Nid "scope")) (Nid "scoped_value"))
  (Nglobal (Nid "Record"))
  (Nscoped (Nglobal (Nid "Record")) (Nid "member_value"))
  (Nglobal (Nanonymous))
  (Nglobal (Nfirst_decl "by_decl"))
  (Nscoped (Nglobal (Nid "Holder")) (Nanon 0))
  (Nscoped (Nglobal (Nid "Holder")) (Nfirst_child "child"))
  (Nglobal (Nid "Alias"))
  (Nglobal (Nid "global_value"))
  (Nglobal (core.Nfunction function_qualifiers.N "unported_function" nil))
  $ { echo 'Require Import skylabs.lang.cpp.mparser.'; echo '#[local] Open Scope pstring_scope.'; echo 'Definition built_names : list Mname := ('; head -n 12 first.out | sed 's/^/  /; s/$/ ::/'; echo '  nil).'; } > check.v
  $ rocq c $ROCQC_ARGS check.v
  $ "$probe" fixture.cpp -- -std=c++17 > second.out 2>/dev/null
  $ cmp first.out second.out

The frozen legacy name-test path remains the oracle. Its direct constructors
agree for simple names; its parser aliases reduce to the probe's explicit
`Nfirst_decl`/`Nfirst_child` core constructors.

  $ cpp2v --name-test=legacy.v fixture.cpp -- -std=c++17 >/dev/null 2>&1
  $ grep -Fq '(Nglobal (Nid "global_value"))' legacy.v
  $ grep -Fq '(Nscoped (Nglobal (Nid "scope")) (Nid "scoped_value"))' legacy.v
  $ grep -Fq '(Nglobal (Nby_first_decl "by_decl"))' legacy.v
  $ grep -Fq '(Nglobal (Nid "Alias"))' legacy.v
  $ grep -Fq '(Nscoped (Nglobal (Nid "Holder")) (Nrecord_by_field "child"))' legacy.v
  $ grep -Fq '(Nscoped (Nglobal (Nid "Holder")) (Nanon 0))' legacy.v
