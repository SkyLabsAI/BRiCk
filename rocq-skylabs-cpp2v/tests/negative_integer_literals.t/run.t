Negative template arguments must be valid Rocq constructor arguments. Exercise
both printing modes and preserve the full range of unsigned literals.

  $ cpp2v -v --check-types --no-sharing --module=unshared.v test.cpp -- -std=c++17
  $ grep -q 'Eint (-1)%Z Tint' unshared.v
  $ grep -q 'Eint (-2147483648)%Z Tint' unshared.v
  $ grep -q 'Eint (-9223372036854775808)%Z' unshared.v
  $ grep -q 'Eint 0%Z Tint' unshared.v
  $ grep -q 'Eint 1%Z Tint' unshared.v
  $ grep -q 'Eint 18446744073709551615%Z' unshared.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix unshared.v
  $ cpp2v -v --check-types --module=shared.v test.cpp -- -std=c++17
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix shared.v
