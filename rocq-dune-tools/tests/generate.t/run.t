  $ mkdir -p workspace/pkg workspace/pkg/elpi workspace/.git/ignored workspace/_build/skipped
  $ cat > workspace/dune <<'EOF'
  > (rocq.theory
  >  (name root.pkg))
  > EOF
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
  $ cat > workspace/custom.flags <<'EOF'
  > -arg -w -arg -custom-flags
  > EOF

  $ dune-rocqproject --root workspace
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  -arg -w -arg -notation-overridden
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/workspace/ root.pkg
  -Q workspace/ root.pkg
  -Q _build/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg
  -Q _build/default/workspace/pkg/elpi/ smoke.elpi

  $ dune-rocqproject --root workspace --prefix vendor --coq-flags custom.flags
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  -arg -w -arg -custom-flags
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/vendor/workspace/ root.pkg
  -Q vendor/workspace/ root.pkg
  -Q _build/default/vendor/workspace/pkg/ smoke.pkg
  -Q vendor/workspace/pkg/ smoke.pkg
  -Q _build/default/vendor/workspace/pkg/elpi/ smoke.elpi
