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
  Stdlib stdpp iris elpi elpi_elpi Ltac2
  skylabs.upoly skylabs.prelude skylabs.iris.extra skylabs.ltac2.extra skylabs.lang.cpp Lens Lens.Elpi))
EOF

cat > dune-project <<EOF
(lang dune 3.21)
(using rocq 0.11)
EOF

export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
export DUNE_CACHE=disabled
