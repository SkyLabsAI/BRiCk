# _CoqProject generator and dune dependency sync

This script will generate an approximate `_CoqProject` file from a dune project, by parsing
all `rocq.theory` stanzas in `dune` files to generate `-Q` mappings.

## Installing dependencies

This script just requires GNU `bash` and `uv` https://docs.astral.sh/uv/.

## Invoke

Run `gen-_CoqProject-dune.sh > _CoqProject` in the `your_dune_workspace` directory.

## Customize Coq warnings

If desired, create a `your_dune_workspace/coq.flags` file containing a
`_CoqProject` snippet, for instance:

```
# Example warning settings:
-arg -w -arg -notation-overridden
```

An absent `coq.flags` is equivalent to an empty one.

## Sync recursive `rocq.theory` dependencies

`sync-rocq-theory-deps.py` rewrites `(theories ...)` fields in `rocq.theory`
stanzas so they include all recursively reachable theory dependencies from the
current Dune workspace, ordered topologically with lexical tie-breaking.

The script:

- finds the Dune workspace root with `dune describe workspace --format=sexp --lang=0.1`
- scans all `dune` files under that workspace root for `rocq.theory` stanzas
- rewrites only `dune` files at or below the directory where the script is run
- fails if any dependency in the recursive closure cannot be uniquely resolved
  to a `rocq.theory` stanza in that workspace

### Invoke

Rewrite files in place:

```sh
./scripts/coq_project_gen/sync-rocq-theory-deps.py
```

Check mode with unified diffs:

```sh
./scripts/coq_project_gen/sync-rocq-theory-deps.py --check
```

### Exit codes

- `0`: success, and in `--check` mode no files would change
- `1`: `--check` found files that would change
- `2`: parse errors, unresolved dependencies, duplicate theory names, cycles, or write failures

### Notes

- The script rewrites only the `(theories ...)` subform and leaves the rest of
  the file byte-identical.
- Formatting inside the rewritten `theories` stanza is normalized to one
  dependency per line.
- Comments inside the old `theories` stanza are not preserved.
- Duplicate logical theory names elsewhere in the workspace are reported when
  they affect the current subtree or a dependency being resolved.
