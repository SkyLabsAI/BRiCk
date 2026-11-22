setup_project() {
cat > dune <<EOF
(env
 (_
  (rocq
   (flags
    (:standard
     ; temporarily disable verbose incompatible prefix warnings
     -w -notation-incompatible-prefix
     ;see https://gitlab.mpi-sws.org/iris/iris/-/blob/master/_CoqProject
     -w -notation-overridden
     ; Similar to notation warnings.
     -w -custom-entry-overridden
     -w -redundant-canonical-projection
     -w -ambiguous-paths
     ; Turn warning on hints into error:
     -w +deprecated-hint-without-locality
     -w +deprecated-instance-without-locality
     -w +unknown-option
     -w +future-coercion-class-field)))))

(rocq.theory
 (name test)
 (theories
  rocq-stdlib rocq-stdpp rocq-iris rocq-elpi rocq-elpi.files
  rocq-core.ltac2 rocq-flocq rocq-upoly rocq-skylabs-prelude
  rocq-skylabs-iris ltac2-extra rocq-skylabs-brick
  rocq-skylabs-brick-cpp-prog rocq-lens rocq-lens-elpi))
EOF

cat > dune-project <<EOF
(lang dune 3.26)
(using rocq 0.15)
EOF
}
