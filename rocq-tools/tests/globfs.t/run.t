  $ rocq compile test.v
  $ cp test.glob test.glob.orig
  $ globfs ls test.glob
  $ globfs cp test.v test.glob:k1.k2
  $ globfs ls test.glob
  test.glob:k1.k2
  $ globfs cp test.v test.glob:k3.k4
  $ globfs ls test.glob
  test.glob:k1.k2
  test.glob:k3.k4
  $ globfs cat test.glob > test.glob.now
  $ diff test.glob.now test.glob.orig
  $ globfs cat test.glob:k1.k2
  Definition one := S O.
  Definition two := S one.
  $ globfs cat test.glob:k3.k4
  Definition one := S O.
  Definition two := S one.
  $ globfs extract test.glob
  $ ls
  test.glob
  test.glob.k1.k2
  test.glob.k3.k4
  test.glob.now
  test.glob.orig
  test.v
  test.vo
  $ diff test.glob.k1.k2 test.v
  $ diff test.glob.k3.k4 test.v
  $ globfs ls test.glob
  test.glob:k1.k2
  test.glob:k3.k4
  $ globfs clear test.glob
  $ diff test.glob test.glob.orig
