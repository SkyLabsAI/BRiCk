--remap-dir=FROM=TO (SkyLabsAI/skylabs-fm#436). pm runs cpp2v in dune's
copy of the project, on the copy of a header, with -I naming the source
tree. Set up that layout by hand: a source tree, cp copies under
_build/default (as dune makes them), cwd = _build/default.

  $ mkdir -p include/lib _build/default/include/lib
  $ printf '#pragma once\n#include "lib/a.h"\n#include "lib/b.h"\n' > include/top.h
  $ printf '#pragma once\nstatic inline int f() { return 0; }\n' > include/lib/a.h
  $ printf '#pragma once\n#include "lib/a.h"\n' > include/lib/b.h
  $ for f in include/top.h include/lib/a.h include/lib/b.h; do cp $f _build/default/$f; done
  $ SRC="$PWD/include"
  $ cd _build/default

Without the flag, "lib/a.h" is reached as the copy (beside top.h) and as
the original (through -I from lib/b.h): two inodes, so `#pragma once`
does not stop the second inclusion.

  $ cpp2v include/top.h -o top.v -- -I"$SRC" -x c++-header -std=c++17 2>&1 | grep -E 'error|note: previous' | sed "s|$SRC|SRC|"
  SRC/lib/a.h:2:19: error: redefinition of 'f'
  $TESTCASE_ROOT/_build/default/include/lib/a.h:2:19: note: previous definition is here
  1 error generated.
  [1]

With the source tree mapped onto the copies, both spellings are one file.

  $ cpp2v --remap-dir=../..=. include/top.h -o top_remap.v -- -I"$SRC" -x c++-header -std=c++17
  $ grep -c Dfunction top_remap.v
  1

The output is the same as a plain run on the source tree.

  $ (cd ../.. && cpp2v include/top.h -o _build/default/top_src.v -- -I"$SRC" -x c++-header -std=c++17)
  $ diff top_remap.v top_src.v

A file with no copy under TO falls back to the source tree.

  $ rm include/lib/b.h
  $ cpp2v --remap-dir=../..=. include/top.h -o top_fallback.v -- -I"$SRC" -x c++-header -std=c++17
  $ diff top_remap.v top_fallback.v

KNOWN LIMITATION (SkyLabsAI/skylabs-fm#436 prototype): that fallback read
is invisible to dune, which only tracks the copies of declared deps;
editing the source b.h now does not rerun a rule like this one.
Expected: the read is tracked, or fails.

  $ printf '#pragma once\n#include "lib/a.h"\nint changed;\n' > "$SRC/lib/b.h"
  $ cpp2v --remap-dir=../..=. include/top.h -o top_fallback2.v -- -I"$SRC" -x c++-header -std=c++17
  $ grep -c changed top_fallback2.v
  1

A malformed mapping is an error.

  $ cpp2v --remap-dir=nonsense include/top.h -o top_bad.v -- -I"$SRC" -x c++-header -std=c++17
  cpp2v: malformed --remap-dir=nonsense (expected FROM=TO)
  [1]
