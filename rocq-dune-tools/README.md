Rocq Dune Tools
===============

This project packages tools for working with Rocq/Dune workspaces:

- `dune-rocqdeps`: rewrite `rocq.theory` dependency stanzas to include
  transitive dependencies

Usage
-----

Synchronize `rocq.theory` dependency stanzas in the current directory subtree:

```sh
dune-rocqdeps
```

Options
-------

For `dune-rocqdeps`:

- `--no-normalize`: only append newly discovered dependencies; preserve the
  existing dependency order and leave files unchanged when nothing new is
  needed
- `--check`: do not edit files; print a `patdiff` against the canonical
  rewrite that `dune-rocqdeps` would produce. The diff may include
  normalization-only changes and need not be the minimal patch that makes
  `--check` pass; the exit status reflects the dependency comparison.
- `--ascii`: when used with `--check`, print diff output without ANSI escape
  codes

`dune-rocqdeps` first looks for `DUNE_SOURCEROOT` or `DUNE_ROOT` in the
environment. When those are absent, it walks upward from the current directory
until it finds a `dune-workspace` or `dune-project` file. It scans all `dune`
files under that workspace root and rewrites only files in the current working
directory subtree.

Rewritten dependency stanzas use this shape:

```lisp
(theories
  direct.dependency
  another.direct.dependency
  ; transitive dependencies
  transitive.dependency more.transitive.dependencies
)
```

In normalized rewrites, the direct section preserves the order from the source
stanza, and the transitive section is sorted alphabetically.

Canonical rewrites may differ textually from other accepted layouts. With
`--check`, use the diff as guidance and trust the exit status.

Once a stanza already uses the `; transitive dependencies` marker, only the
entries before that marker are treated as direct roots on the next run. That
means removing a direct dependency and rerunning the tool automatically drops
stale transitive dependencies from the rewritten closure.
