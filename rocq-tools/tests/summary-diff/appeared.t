  $ cat > base.csv <<EOF
  > File,instructions
  > c,8000000000
  > d,16000000000
  > EOF

  $ cat > job.csv <<EOF
  > File,instructions
  > a,2000000000
  > b,4000000000
  > c,8000000000
  > d,16000000000
  > EOF

  $ rocq-perf.summary-diff --no-colors --instr-threshold 0 --markdown base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |  +25.00% |     24.0 |     30.0 |     +6.0 | total
  |  +20.00% |        - |      6.0 |     +6.0 | ├ newly appeared files (2)
  |   +0.00% |     24.0 |     24.0 |     +0.0 | └ common files
  |   +0.00% |     24.0 |     24.0 |     +0.0 | └ proofs and tests
