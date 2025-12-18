  $ cat > dune-log.json <<EOF
  > [
  >   {
  >     "command": "(cd _build/.sandbox/d408abfb52ef45bc73a852a1f418a0a5/default && /usr/bin/sh -c 'patdiff -keep-whitespace -location-style omake -ascii fmdeps/auto/coq-skylabs-auto-cpp/cram/arith_bug.t/run.t fmdeps/auto/coq-skylabs-auto-cpp/cram/arith_bug.t/run.t.corrected')",
  >     "output": [
  >       "------ fmdeps/auto/coq-skylabs-auto-cpp/cram/arith_bug.t/run.t",
  >       "++++++ fmdeps/auto/coq-skylabs-auto-cpp/cram/arith_bug.t/run.t.corrected",
  >       "File \"fmdeps/auto/coq-skylabs-auto-cpp/cram/arith_bug.t/run.t\", line 5, characters 0-1:",
  >       " |  $ DUNE_CACHE=disabled dune build bug.vo 2>&1",
  >       " |  File \"./bug.v\", line 43, characters 4-37:",
  >       " |  Error: Timeout!", " |  ",
  >       "-|  File \"./bug.v\", line 45, characters 4-37:",
  >       "+|  File \"./bug.v\", line 43, characters 4-37:", " |  Warning:",
  >       " |  Ill-formed log (Log.collect: span \"arith_solve\" is still open.), using debug mode.",
  >       " |  [sl-ill-formed-log,default]", " |  [1]"
  >     ],
  >     "status": 1
  >   }
  > ]
  > EOF
  $ coqc-perf.code-quality-diff --after-dune dune-log.json
  # Changes in Warnings or Errors
  |        |Before|New |Fixed|After|
  |--------|-----:|---:|----:|----:|
  |Errors  | 0   | 1 | 0  | 1  |
  |Warnings| 0   | 0 | 0  | 0  |
  
  <details open><summary>
  
  ## :x: New Errors (1)
  
  </summary>
  
  ```
  File "fmdeps/auto/coq-skylabs-auto-cpp/cram/arith_bug.t/run.t", line 5, characters 0-1:
   |  $ DUNE_CACHE=disabled dune build bug.vo 2>&1
   |  File "./bug.v", line 43, characters 4-37:
   |  Error: Timeout!
   |  
  -|  File "./bug.v", line 45, characters 4-37:
  +|  File "./bug.v", line 43, characters 4-37:
   |  Warning:
   |  Ill-formed log (Log.collect: span "arith_solve" is still open.), using debug mode.
   |  [sl-ill-formed-log,default]
   |  [1]
  ```
  
  </details>
  
