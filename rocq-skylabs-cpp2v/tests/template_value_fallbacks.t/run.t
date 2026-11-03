These defensive paths cannot be selected by well-formed template references.
Exercise the actual printer directly and ask Rocq to check every emitted term.
  $ ../../build-dune/printer-tests/cpp2v-fallback-tests > fallbacks.v 2>diagnostics.log
  $ cat checks.v >> fallbacks.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix fallbacks.v
