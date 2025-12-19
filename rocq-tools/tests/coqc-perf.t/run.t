  $ . ../setup.sh

Generating test files.

  $ ocaml gen.ml 1    > small.v
  $ ocaml gen.ml 7    > medium.v
  $ ocaml gen.ml 200  > large.v
  $ ocaml gen.ml 1000 > huge.v
  $ wc -l *.v
       5 err_out.v
    9976 huge.v
    1976 large.v
      46 medium.v
      46 medium_variation.v
       7 small.v
   12056 total

Running coqc

  $ coqc -color on small.v
  $ coqc -color on medium.v
  $ coqc -color on large.v
  $ coqc -color on huge.v
  $ coqc -color on medium_variation.v
  $ coqc -color on err_out.v 2>&1
  File "./err_out.v", line 3, characters 6-20:
  Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]
  nat : Set
  
  nat is not universe polymorphic
  Expands to: Inductive Corelib.Init.Datatypes.nat
  Declared in library Corelib.Init.Datatypes, line 178, characters 10-13
  $ rm *.vo *.glob *.vos *.vok

Running our coqc wrapper

  $ coqc-perf -color on small.v
  $ coqc-perf -color on medium.v
  $ coqc-perf -color on large.v
  $ coqc-perf -color on huge.v
  $ coqc-perf -color on medium_variation.v
  $ coqc-perf -color on err_out.v > out.txt 2> err.txt
  $ cat out.txt
  nat : Set
  
  nat is not universe polymorphic
  Expands to: Inductive Corelib.Init.Datatypes.nat
  Declared in library Corelib.Init.Datatypes, line 178, characters 10-13
  $ cat err.txt
  File "./err_out.v", line 3, characters 6-20:
  Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]
  $ rm *.vos *.vok

Extracting all the data

  $ globfs extract small.glob
  $ globfs extract medium.glob
  $ globfs extract large.glob
  $ globfs extract huge.glob
  $ globfs extract medium_variation.glob
  $ globfs extract err_out.glob
  $ ls *.v* *.glob*
  err_out.glob
  err_out.glob.perf.csvline
  err_out.glob.perf.json
  err_out.glob.stderr
  err_out.glob.stdout
  err_out.v
  err_out.vo
  huge.glob
  huge.glob.perf.csvline
  huge.glob.perf.json
  huge.v
  huge.vo
  large.glob
  large.glob.perf.csvline
  large.glob.perf.json
  large.v
  large.vo
  medium.glob
  medium.glob.perf.csvline
  medium.glob.perf.json
  medium.v
  medium.vo
  medium_variation.glob
  medium_variation.glob.perf.csvline
  medium_variation.glob.perf.json
  medium_variation.v
  medium_variation.vo
  small.glob
  small.glob.perf.csvline
  small.glob.perf.json
  small.v
  small.vo

Build CSV summary

  $ coqc-perf.csv-summary > summary.csv
  $ wc -l summary.csv
  7 summary.csv

Adding noise

  $ coqc-perf.add-noise 0.05 small.glob.perf.json small.glob.perf.json.5p
  $ coqc-perf.add-noise 0.05 medium.glob.perf.json medium.glob.perf.json.5p
  $ coqc-perf.add-noise 0.05 large.glob.perf.json large.glob.perf.json.5p
  $ coqc-perf.add-noise 0.05 huge.glob.perf.json huge.glob.perf.json.5p
  $ coqc-perf.add-noise 0.05 medium_variation.glob.perf.json medium_variation.glob.perf.json.5p

Test webpage

  $ coqc-perf.html-diff small.v small.glob.perf.json small.v small.glob.perf.json.5p > small.html
  $ coqc-perf.html-diff medium.v medium.glob.perf.json medium.v medium.glob.perf.json.5p > medium.html
  $ coqc-perf.html-diff large.v large.glob.perf.json large.v large.glob.perf.json.5p > large.html
  $ coqc-perf.html-diff huge.v huge.glob.perf.json huge.v huge.glob.perf.json.5p > huge.html

  $ coqc-perf.html-diff small.v small.glob.perf.json medium.v medium.glob.perf.json.5p > medium_small_ref.html
  $ coqc-perf.html-diff medium.v medium.glob.perf.json small.v small.glob.perf.json.5p > medium_small_src.html

  $ coqc-perf.html-diff medium.v medium.glob.perf.json medium_variation.v medium_variation.glob.perf.json.5p > medium_medium_variation.html
