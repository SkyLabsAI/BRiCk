Rocq Dune Tools
===============

This project packages a small OCaml executable, `dune-rocqproject`, for
generating `_CoqProject` content from a Rocq/Dune workspace.

Usage
-----

Generate the full `_CoqProject` content for the current directory:

```sh
dune-rocqproject
```

Options
-------

- `--root DIR`: choose the workspace root to scan
- `--prefix PREFIX`: prepend a path prefix to emitted mappings
- `--coq-flags FILE`: choose the optional flags file to splice into the output
