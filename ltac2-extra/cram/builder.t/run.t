  $ export PATH="$DUNE_SOURCEROOT/_build/install/default/bin:$PATH"
  $ DUNE_CACHE=disabled dune build test1.vo 2>&1
  File "dune", lines 12-32, characters 0-478:
  12 | (rocq.theory
  13 |   (name skylabs_auto.cram.builder) ; logical path of this library
  14 |   ; skylabs deps
  ....
  30 |     skylabs.elpi.extra
  31 |     skylabs.elpi.cpp
  32 |     skylabs))
  (** Test 1 - no errors *)
  - : unit = ()
  
  (** Test 2 - error in function application *)
  File "./test1.v", line 30, characters 4-305:
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
  File "dune", lines 12-32, characters 0-478:
  12 | (rocq.theory
  13 |   (name skylabs_auto.cram.builder) ; logical path of this library
  14 |   ; skylabs deps
  ....
  30 |     skylabs.elpi.extra
  31 |     skylabs.elpi.cpp
  32 |     skylabs))
  
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

