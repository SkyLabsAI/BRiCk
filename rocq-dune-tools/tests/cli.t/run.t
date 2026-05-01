  $ dune-rocqproject --help
  Usage:
    dune-rocqproject [generate-coq-project] [--root DIR] [--prefix PREFIX] [--coq-flags FILE]
    dune-rocqproject gather-coq-paths [--prefix PREFIX] DUNE_FILE...
  
  Default command:
    generate-coq-project

  $ mkdir -p workspace/pkg workspace/pkg/elpi workspace/.git/ignored workspace/_build/skipped
  $ cat > workspace/pkg/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.pkg))
  > EOF
  $ cat > workspace/pkg/elpi/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.elpi))
  > EOF
  $ cat > workspace/.git/ignored/dune <<'EOF'
  > (rocq.theory
  >  (name ignored.git))
  > EOF
  $ cat > workspace/_build/skipped/dune <<'EOF'
  > (rocq.theory
  >  (name ignored.build))
  > EOF
  $ cat > workspace/coq.flags <<'EOF'
  > -arg -w -arg -notation-overridden
  > EOF

  $ dune-rocqproject gather-coq-paths workspace/pkg/dune
  -Q _build/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg

  $ dune-rocqproject gather-coq-paths workspace/pkg/elpi/dune
  -Q _build/default/workspace/pkg/elpi/ smoke.elpi

  $ dune-rocqproject --root workspace
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  -arg -w -arg -notation-overridden
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/pkg/ smoke.pkg
  -Q pkg/ smoke.pkg
  -Q _build/default/pkg/elpi/ smoke.elpi

  $ dune-rocqproject --root workspace --prefix vendor
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  -arg -w -arg -notation-overridden
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/vendor/pkg/ smoke.pkg
  -Q vendor/pkg/ smoke.pkg
  -Q _build/default/vendor/pkg/elpi/ smoke.elpi
