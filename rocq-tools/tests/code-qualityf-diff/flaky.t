  $ mkdir before after

  $ cat > before/test.glob.stderr <<EOF
  > File "test.v", line 100, characters 8-25:
  > Warning: Timeout (2.50s) exceeded: tactic ran for 3.98s [sl-work-timeout,sl]
  > EOF

  $ cat > after/test.glob.stderr <<EOF
  > File "test.v", line 100, characters 8-25:
  > Warning: Timeout (2.50s) exceeded: tactic ran for 3.71s [sl-work-timeout,sl]
  > EOF

  $ echo "before/test.glob.stderr" > before-globs
  $ echo "after/test.glob.stderr" > after-globs

  $ coqc-perf.code-quality-diff --before-globs-from-file before-globs --after-globs-from-file after-globs
  # No Changes in Warnings or Errors
  |        |Before|New |Fixed|After|
  |--------|-----:|---:|----:|----:|
  |Errors  | 0   | 0 | 0  | 0  |
  |Warnings| 1   | 0 | 0  | 1  |
  
