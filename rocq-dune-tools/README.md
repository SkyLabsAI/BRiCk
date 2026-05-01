Rocq Dune Tools
===============

This project packages a small OCaml executable, `dune-rocqproject`, for
generating `_CoqProject` content from a Rocq/Dune workspace.

It replaces the behavior of:

- `scripts/coq_project_gen/gather-coq-paths.py`
- `scripts/coq_project_gen/gen-_CoqProject-dune.sh`

Usage
-----

Generate the full `_CoqProject` content for the current directory:

```sh
dune-rocqproject
```

Explicit subcommand form:

```sh
dune-rocqproject generate-coq-project
```

Print only the `-Q` mappings for selected `dune` files:

```sh
dune-rocqproject gather-coq-paths path/to/dune another/path/dune
```

Options
-------

- `--root DIR`: choose the workspace root to scan
- `--prefix PREFIX`: prepend a path prefix to emitted mappings
- `--coq-flags FILE`: choose the optional flags file to splice into the output
