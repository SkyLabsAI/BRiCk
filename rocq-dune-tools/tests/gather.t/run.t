  $ mkdir -p workspace/pkg workspace/pkg/elpi workspace/plain workspace/.git/ignored
  $ cat > workspace/pkg/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.pkg))
  > EOF
  $ cat > workspace/pkg/elpi/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.elpi))
  > EOF
  $ cat > workspace/plain/dune <<'EOF'
  > (library
  >  (name plain))
  > EOF
  $ cat > workspace/.git/ignored/dune <<'EOF'
  > (rocq.theory
  >  (name ignored.git))
  > EOF

  $ dune-rocqproject gather-coq-paths workspace/pkg/dune
  -Q _build/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg

  $ dune-rocqproject gather-coq-paths workspace/pkg/elpi/dune
  -Q _build/default/workspace/pkg/elpi/ smoke.elpi

  $ dune-rocqproject gather-coq-paths --prefix vendor workspace/pkg/dune
  -Q _build/default/vendor/workspace/pkg/ smoke.pkg
  -Q vendor/workspace/pkg/ smoke.pkg

  $ dune-rocqproject gather-coq-paths workspace/plain/dune

  $ dune-rocqproject gather-coq-paths workspace/.git/ignored/dune
