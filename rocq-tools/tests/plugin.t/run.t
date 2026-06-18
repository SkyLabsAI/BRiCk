Building the project.

  $ DUNE_CACHE=disabled dune build --display=quiet
  File "./test.v", line 3, characters -2--2:
  Warning: Not interpreting "*)" as the end of current non-terminated comment
  because it occurs in a non-terminated string of the comment.
  [comment-terminator-in-string,parsing,default]
  $ globfs ls _build/default/test.glob
  _build/default/test.glob:feedback.json
  _build/default/test.glob:perf.json
  $ globfs cat _build/default/test.glob:feedback.json
  [ null, null, null, null, null, null, null, null, null, null, null ]
  $ globfs cat _build/default/test.glob:perf.json | jq '.traceEvents.[].name' | wc -l
  214
