  $ cat > dune-log.json <<EOF
  > [
  >   {
  >     "command": "_build/default/vendored/rocq/topbin/coqc_bin.exe --config > /tmp/dune_6f9dd0_output",
  >     "output": [],
  >     "status": 1
  >   },
  >   {
  >     "command": "(cd _build/default && fmdeps/BRiCk/ltac2-extra/.bin/coqc -q -w <.. a spurious appearance of extra.v ..> fmdeps/BRiCk/ltac2-extra/theories/extra.v)",
  >     "output": [
  >       "what",
  >       "File \"./fmdeps/BRiCk/ltac2-extra/theories/extra.v\", line 43, characters 8-17:",
  >       "Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]",
  >       "File \"./fmdeps/BRiCk/ltac2-extra/theories/extra.v\", line 44, characters 19-20:",
  >       "Error: Syntax error: '.' expected after [command] (in [vernac_aux]).",
  >       ""
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
  |Warnings| 0   | 2 | 0  | 2  |
  
  <details open><summary>
  
  ## :x: New Errors (1)
  
  </summary>
  
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  </details>
  
  <details open><summary>
  
  ## :warning: New Warnings (2)
  
  </summary>
  
  ```
  File "fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 0, characters 0-0:
  Warning: Dangling output when building using coqc:
  what
  [dangling-output-stdout,dummy]
  ```
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 43, characters 8-17:
  Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]
  ```
  
  </details>
  

  $ coqc-perf.code-quality-diff --before-dune dune-log.json
  # Changes in Warnings or Errors
  |        |Before|New |Fixed|After|
  |--------|-----:|---:|----:|----:|
  |Errors  | 1   | 0 | 1  | 0  |
  |Warnings| 2   | 0 | 2  | 0  |
  
  <details><summary>
  
  ## :negative_squared_cross_mark: Fixed Errors (1)
  
  </summary>
  
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  </details>
  
  <details><summary>
  
  ## :green_heart: Fixed Warnings (2)
  
  </summary>
  
  ```
  File "fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 0, characters 0-0:
  Warning: Dangling output when building using coqc:
  what
  [dangling-output-stdout,dummy]
  ```
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 43, characters 8-17:
  Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]
  ```
  
  </details>
  
