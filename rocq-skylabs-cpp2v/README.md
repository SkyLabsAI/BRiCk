Code generator for the BRiCk program logic for C++
==================================================

## Dependencies

The dependencies for the code generator are the following:
- A C++ compiler
- The `cmake` tool
- LLVM 16 or greater (the tool is well tested up to version 18)

### Native dependencies: Linux (Ubuntu)

Install the dependencies:
```sh
sudo apt install cmake build-essential
```

Install LLVM 18 following [these directions](https://apt.llvm.org/):
```sh
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 18 all
```

### Native dependencies: OSX

For OSX we recommend clang 18:
```sh
brew install llvm@18 cmake opam
export PATH=/usr/local/opt/llvm@18/bin:${PATH}
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
following command produces files `NAMES_FILE` and `AST_FILE`.
```sh
./build/cpp2v -v -names ${NAMES_FILE} -o ${AST_FILE} ${CPP_SOURCE} -- ${FLAGS}
```
For a `CPP_SOURCE` named `file.cpp`, a convention that is often followed is
to define `AST_FILE` as `file_cpp.v`, and `NAMES_FILE` as `file_cpp_names.v`.

### After building with `dune`

You can use the following to invoke the `cpp2v` program with the given list of
arguments `ARGS`.
```
dune exec -- cpp2v ${ARGS}
```

## Directory layout

Directories `src` and `include` hold the implementation of the `cpp2v`. The
directory `llvm-include` additionally contain extensions of LLVM source code
(see [llvm-include/LICENSE.txt](llvm-include/LICENSE.txt) for the license that
is associated to these files).
