  $ mkdir -p workspace/pkg workspace/fmdeps/cpp2v-core/rocq-skylabs-brick/tests
  $ cat > workspace/pkg/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.pkg))
  > EOF
  $ cat > workspace/bad.dune <<'EOF'
  > (rocq.theory
  >  (name broken)
  > EOF

  $ dune-rocqproject --root workspace/missing 2>&1 | sed -n '1p'
  error: workspace/missing/ is not a directory

  $ dune-rocqproject gather-coq-paths workspace/bad.dune 2>&1 | sed -n '1p'
  error: workspace/bad.dune: Failure("Sexplib.Sexp.input_rev_sexps: reached EOF while in state Parsing_list")

  $ dune-rocqproject --root workspace --coq-flags absent.flags
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg
  -Q fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest
  -Q _build/default/fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest
