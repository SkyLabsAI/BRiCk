  $ export PATH="$DUNE_SOURCEROOT/_build/install/default/bin:$PATH"
  $ DUNE_CACHE=disabled dune build test1.vo 2>&1
  File "dune", lines 12-18, characters 0-148:
  12 | (rocq.theory
  13 |   (name skylabs.ltac2.extra.cram.builder) ; logical path of this library
  14 |   (theories
  15 |     Stdlib
  16 |     Ltac2
  17 |     skylabs.ltac2.extra
  18 |    ))
  (** Test 1 - no errors *)
  - : unit = ()
  
  (** Test 2 - error in function application *)
  File "./test1.v", line 29, characters 4-305:
  Error:
  Uncaught Ltac2 exception:
  Control.ErrorCxt
  message:(
    context:  faulty list builder
    
    context:  Builder.Ap.apply
    
    context:
      Error when checking argument types
        function:  (fun (a : list ?A) (b : ?A) (c : list ?A) =>
                    a ++ [b] ++ List.rev c)
        type:      (list ?A -> ?A -> list ?A -> list ?A)
        arguments: ? : nat
                   ? : nat
                   ? : (list nat))
  (Internal err:(Unable to unify "nat" with "list ?A".))
  
  [1]
  $ DUNE_CACHE=disabled dune build test2.vo 2>&1
  File "dune", lines 12-18, characters 0-148:
  12 | (rocq.theory
  13 |   (name skylabs.ltac2.extra.cram.builder) ; logical path of this library
  14 |   (theories
  15 |     Stdlib
  16 |     Ltac2
  17 |     skylabs.ltac2.extra
  18 |    ))
  
  (** Test 3 - error in arguments *)
  File "./test2.v", line 19, characters 4-307:
  Error:
  Uncaught Ltac2 exception:
  Control.ErrorCxt
  message:(
    context:  constr builder for type nat
                invalid argument: [1])
  (Internal
    err:(The term "[1]" has type "list nat" while it is expected to have type
          "nat".))
  
  [1]

