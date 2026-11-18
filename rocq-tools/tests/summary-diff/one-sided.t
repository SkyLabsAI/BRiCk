Files present on one side only are listed in the details, filtered by the
instruction threshold alone: new files last (biggest last), removed files
first (biggest first).

  $ cat > base.csv <<EOF
  > File,instructions
  > common_up.v,10000000000
  > common_down.v,10000000000
  > gone_big.v,5000000000
  > gone_small.v,500000000
  > gone_mid.v,2000000000
  > EOF

  $ cat > job.csv <<EOF
  > File,instructions
  > common_up.v,12000000000
  > common_down.v,9000000000
  > new_small.v,300000000
  > new_big.v,7000000000
  > new_mid.v,1500000000
  > EOF

  $ rocq-perf.summary-diff --no-colors --instr-threshold 1 --markdown base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |     gone |      5.0 |        - |     -5.0 | gone_big.v
  |     gone |      2.0 |        - |     -2.0 | gone_mid.v
  |  -10.00% |     10.0 |      9.0 |     -1.0 | common_down.v
  |  +20.00% |     10.0 |     12.0 |     +2.0 | common_up.v
  |      new |        - |      1.5 |     +1.5 | new_mid.v
  |      new |        - |      7.0 |     +7.0 | new_big.v
  |   +8.36% |     27.5 |     29.8 |     +2.3 | total
  |  -20.66% |      7.5 |        - |     -7.5 | ├ disappeared files (3)
  |  +23.59% |        - |      8.8 |     +8.8 | ├ newly appeared files (3)
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ common files
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ proofs and tests

  $ rocq-perf.summary-diff --no-colors --instr-threshold 1 --github base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |   +8.36% |     27.5 |     29.8 |     +2.3 | total
  |  -20.66% |      7.5 |        - |     -7.5 | ├ disappeared files (3)
  |  +23.59% |        - |      8.8 |     +8.8 | ├ newly appeared files (3)
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ common files
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ proofs and tests
  
  <details><summary>Full Results</summary>
  
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |     gone |      5.0 |        - |     -5.0 | gone_big.v
  |     gone |      2.0 |        - |     -2.0 | gone_mid.v
  |  -10.00% |     10.0 |      9.0 |     -1.0 | common_down.v
  |  +20.00% |     10.0 |     12.0 |     +2.0 | common_up.v
  |      new |        - |      1.5 |     +1.5 | new_mid.v
  |      new |        - |      7.0 |     +7.0 | new_big.v
  |          |          |          |          |          
  |   +8.36% |     27.5 |     29.8 |     +2.3 | total
  |  -20.66% |      7.5 |        - |     -7.5 | ├ disappeared files (3)
  |  +23.59% |        - |      8.8 |     +8.8 | ├ newly appeared files (3)
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ common files
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ proofs and tests
  
  </details>

Small files are shown with --show-all.

  $ rocq-perf.summary-diff --no-colors --instr-threshold 1 --show-all --markdown base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |     gone |      5.0 |        - |     -5.0 | gone_big.v
  |     gone |      2.0 |        - |     -2.0 | gone_mid.v
  |     gone |      0.5 |        - |     -0.5 | gone_small.v
  |  -10.00% |     10.0 |      9.0 |     -1.0 | common_down.v
  |  +20.00% |     10.0 |     12.0 |     +2.0 | common_up.v
  |      new |        - |      0.3 |     +0.3 | new_small.v
  |      new |        - |      1.5 |     +1.5 | new_mid.v
  |      new |        - |      7.0 |     +7.0 | new_big.v
  |   +8.36% |     27.5 |     29.8 |     +2.3 | total
  |  -20.66% |      7.5 |        - |     -7.5 | ├ disappeared files (3)
  |  +23.59% |        - |      8.8 |     +8.8 | ├ newly appeared files (3)
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ common files
  |   +5.00% |     20.0 |     21.0 |     +1.0 | └ proofs and tests

The CSV output keeps its raw format: one-sided files have a zero change.

  $ rocq-perf.summary-diff --csv base.csv job.csv
  Relative (%),Master (instr),MR (instr),Change (instr),Filename
  -10.000000,10000000000,9000000000,-1000000000,common_down.v
  0.000000,5000000000,5000000000,0,gone_big.v
  0.000000,2000000000,2000000000,0,gone_mid.v
  0.000000,500000000,500000000,0,gone_small.v
  0.000000,7000000000,7000000000,0,new_big.v
  0.000000,1500000000,1500000000,0,new_mid.v
  0.000000,300000000,300000000,0,new_small.v
  20.000000,10000000000,12000000000,2000000000,common_up.v
  5.000000,20000000000,21000000000,1000000000,*
