  $ mkdir globs
  $ cat > globs/test.glob.stderr <<EOF
  > File "test.v", line 44, characters 19-20:
  > Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  > EOF
  $ cat > globs/test.glob.stdout <<EOF
  > dangling text!
  > EOF
  $ cat > globs/files <<EOF
  > globs/test.glob.stderr
  > globs/test.glob.stdout
  > EOF
  $ coqc-perf.code-quality-diff --after-globs-from-file globs/files
  # Changes in Warnings or Errors
  |        |Before|New |Fixed|After|
  |--------|-----:|---:|----:|----:|
  |Errors  | 0   | 1 | 0  | 1  |
  |Warnings| 0   | 1 | 0  | 1  |
  
  <details open><summary>
  
  ##  Rocq Files with Errors (1)
  
  </summary>
  
  ```
  # Files with new errors
  - test.v
  ```
  </details>
  
  <details open><summary>
  
  ## :x: New Errors (1)
  
  </summary>
  
  ```
  File "test.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  </details>
  
  <details open><summary>
  
  ## :warning: New Warnings (1)
  
  </summary>
  
  ```
  File "test.v", line 0, characters 0-0:
  Warning: Non-empty stdout when building using coqc:
  dangling text!
  [non-empty-stdout,dummy]
  ```
  
  </details>
  

  $ coqc-perf.code-quality-diff --before-globs-from-file globs/files
  # Changes in Warnings or Errors
  |        |Before|New |Fixed|After|
  |--------|-----:|---:|----:|----:|
  |Errors  | 1   | 0 | 1  | 0  |
  |Warnings| 1   | 0 | 1  | 0  |
  
  <details><summary>
  
  ## :negative_squared_cross_mark: Fixed Errors (1)
  
  </summary>
  
  ```
  File "test.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  </details>
  
  <details><summary>
  
  ## :green_heart: Fixed Warnings (1)
  
  </summary>
  
  ```
  File "test.v", line 0, characters 0-0:
  Warning: Non-empty stdout when building using coqc:
  dangling text!
  [non-empty-stdout,dummy]
  ```
  
  </details>
  
