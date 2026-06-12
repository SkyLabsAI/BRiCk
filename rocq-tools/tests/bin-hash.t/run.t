  $ printf 'bin-hash test data\n' > test-bin
  $ chmod +x test-bin
  $ export PATH="$PWD:$PATH"

  $ bin-hash --ocaml test_hash test-bin
  let test_hash = "4d3b619ef25836df47b0e038b25121dd"

  $ bin-hash --rocq test_hash test-bin
  Require Import PrimString.
  
  Definition test_hash := "4d3b619ef25836df47b0e038b25121dd"%pstring.

  $ bin-hash --sh TEST_HASH test-bin
  TEST_HASH="4d3b619ef25836df47b0e038b25121dd"
