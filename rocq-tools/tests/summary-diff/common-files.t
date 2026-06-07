  $ cat > base.csv <<EOF
  > File,instructions
  > common,10000000000
  > gone,2000000000
  > EOF

  $ cat > job.csv <<EOF
  > File,instructions
  > common,15000000000
  > new,3000000000
  > EOF

  $ coqc-perf.summary-diff --no-colors --instr-threshold 0 --markdown base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |  +50.00% |     10.0 |     15.0 |     +5.0 | common
  |  +50.00% |     12.0 |     18.0 |     +6.0 | total
  |  -13.33% |      2.0 |        - |     -2.0 | ├ disappeared files (1)
  |  +15.00% |        - |      3.0 |     +3.0 | ├ newly appeared files (1)
  |  +50.00% |     10.0 |     15.0 |     +5.0 | └ common files
  |  +50.00% |     10.0 |     15.0 |     +5.0 | └ proofs and tests
