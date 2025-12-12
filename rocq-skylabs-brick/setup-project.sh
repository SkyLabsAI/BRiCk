cat > dune <<EOF
(env
 (_
  (coq
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

(coq.theory
 (name test)
 (theories
  Stdlib stdpp iris elpi elpi_elpi Ltac2
  bluerock.upoly bluerock.prelude bluerock.iris.extra bluerock.ltac2.extra bluerock.lang.cpp Lens Lens.Elpi))
EOF

cat > dune-project <<EOF
(lang dune 3.8)
(using coq 0.8)
EOF

export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
export DUNE_CACHE=disabled
