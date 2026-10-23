Code generator for the BRiCk program logic for C++
==================================================

## Dependencies

The dependencies for the code generator are the following:
- A C++ compiler
- The `cmake` tool
- LLVM 20 to 22 (other versions aren't tested in CI)

### Native dependencies: Linux (Ubuntu)

Install the dependencies:
```sh
sudo apt install cmake build-essential
```

Install LLVM 22 following [these directions](https://apt.llvm.org/):
```sh
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 22 all
export PATH=/usr/lib/llvm-22/bin:${PATH}
```

### Native dependencies: OSX

For OSX we recommend clang 22:
```sh
brew install llvm@22 cmake opam
export PATH=$(brew --prefix llvm@22)/bin:${PATH}
```

## Building

### With the `Makefile`

For building, you should be able to simply run:
```
make -j8
```
which will produce executable `build/cpp2v`.

### With `dune`

Simply run `dune build @cpp2v`.

This assumes that [dune](https://github.com/ocaml/dune) is available.

## Running

### After building with the `Makefile`

Given a C++ source file `CPP_SOURCE`, and a set of compiler flags `FLAGS`, the
following command produces file `AST_FILE`.
```sh
./build/cpp2v -v -o ${AST_FILE} ${CPP_SOURCE} -- ${FLAGS}
```
For a `CPP_SOURCE` named `file.cpp`, a convention that is often followed is
to define `AST_FILE` as `file_cpp.v`.

### After building with `dune`

You can use the following to invoke the `cpp2v` program with the given list of
arguments `ARGS`.
```
dune exec -- cpp2v ${ARGS}
```

## Shared host/Docker execution

The package also installs `cpp2v-run` and `cpp2v-toolchain` for running commands
and generating command adapters against a common host/container environment.
They support explicit TU translation, compilation, and executable tests. Inline
`cpp.prog` translation remains host-only. Docker is opt-in; image choices and
forwarded environment variables remain consumer configuration. See [scripts/README.md](scripts/README.md).

## Directory layout

Directories `src` and `include` hold the implementation of the `cpp2v`. The
directory `llvm-include` additionally contain extensions of LLVM source code
(see [llvm-include/LICENSE.txt](llvm-include/LICENSE.txt) for the license that
is associated to these files).
