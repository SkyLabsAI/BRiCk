# BRiCk

A program logic for verifying concurrent C++ in Rocq.

## Build & Dependencies

### Building

Building is done via [dune](https://github.com/ocaml/dune) and can be done
using

```sh
$ dune build
```

### Building docs

Run `make -C .. doc`.

## Examples

See the examples in the `tests` directory to get an idea of coverage that the
logic supports. More examples will be added as the feature set evolves.

You can run the tests with:
```sh
$ dune runtest
```

## Repository Layout

- `theories` -- the core Rocq development.
  - `lang/cpp` -- the C++ syntax and semantics
    - `syntax` -- the definition of the C++ AST (abstract syntax tree)
    - `semantics` -- core semantic definitions that are independent of separation logic
    - `logic` -- the separation logic weakest pre-condition semantics
    - `parser` -- the environment used to interpret the generated code.

The prelude extending [stdpp](https://gitlab.mpi-sws.org/iris/stdpp) lives in
the separate package `rocq-skylabs-prelude` (`../rocq-skylabs-prelude`).

## Rocq IDEs

`dune build` generates a `_RocqProject` file next to each theory's `dune` file
(e.g. `theories/lang/cpp/_RocqProject`) for use by Rocq IDEs.
