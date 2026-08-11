Code generator for the BRiCk program logic for C++
==================================================

## Dependencies

The dependencies for the code generator are the following:
- A C++ compiler
- The `cmake` tool
- LLVM 16 or greater (the tool is tested through version 22)

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
following command produces `AST_FILE`:

```sh
./build/cpp2v -v -o ${AST_FILE} ${CPP_SOURCE} -- ${FLAGS}
```

For a `CPP_SOURCE` named `file.cpp`, `file_cpp.v` is a common `AST_FILE` name.
The isolated `--name-test ${NAMES_FILE}` option can additionally emit structured
names for diagnostics; it is not a second semantic-output backend.

### After building with `dune`

You can use the following to invoke the `cpp2v` program with the given list of
arguments `ARGS`.
```
dune exec -- cpp2v ${ARGS}
```

## Source-location companions

Pass `--locations` together with a named module output to produce a standalone
source-location companion from the same validated translation-unit IR as the
ordinary AST:

```sh
cpp2v -o file_cpp.v --locations file_cpp_locations.v file.cpp -- -std=c++17
```

`--locations` requires `--module`/`-o`. Neither output may be `-`, the two paths
must differ, and location output is incompatible with `--for-interactive`.
Without `--locations`, cpp2v creates no companion and retains its ordinary CLI
behavior.

The files are published serially and atomically per path through a temporary
`.partial` file and rename. The AST is published first. If companion generation
or publication fails, the already-published AST may remain, but the final
location path is not published.

### Generated value and root kinds

The ordinary AST output exports `source` (with deprecated parsing abbreviation
`module` for compatibility). The companion imports the BRiCk source-location
API and contains local `source_files`, normalized indexed provenance tables,
an exact indexed location DAG, and `located_root_events` construction values.
The location DAG hash-conses complete `(ordered origin IDs, ordered child node
IDs)` rows child-before-parent and separately interns exact structural shape
certificates. Root events carry only static node/shape IDs; equal duplicates
build lazy recursive merge views, while unequal winners retain losing origins
only at the root. DAG identities never enter public paths. Provenance uses
deterministic first-seen primitive-array chunks and private primitive `uint63`
IDs for
presumed filenames, points, ranges, macro frames when their table is strictly
smaller than inline occurrences, and origin rows. `lookup` lazily decodes only
selected origin rows. Direct projection of an origin list is unsupported;
`files` remains directly available, and
`Internal.materialize_origins` is an explicitly eager diagnostic/test helper.
Malformed private provenance IDs report `MalformedProvenance`; malformed DAG
rows, shapes, storage, or non-backward edges report `MalformedLocationDag` only
when reached. Valid generated maps preserve lookup values, order, and public
errors. Public `file_id` and
`origin_id` values are distinct nominal wrappers around primitive `uint63`
integers rather than unary `nat`; explicit literals may use the `%file_id` and
`%origin_id` scopes. `lookup_file source_locations id` performs checked file
access without converting a potentially large primitive ID to unary `nat`.
Semantic child paths remain `list nat`, while byte offsets, lines, and columns
remain binary, nonnegative `N` values. Construction only VM-reduces compact
root-event folding and never reads or expands provenance or location tables. Its only
public generated value is:

```coq
source_locations : source_map
```

It is standalone: semantic root names and values are inline and it neither
imports the AST output nor refers to that file's sharing definitions. The map
has four distinct root namespaces, selected with a `decl_root`:

- `DRSymbol name` — ordinary object/function symbol;
- `DRType name` — ordinary type/global declaration;
- `DRMsymbol name` — template object/function symbol; and
- `DRMtype name` — template type/global declaration.

Use the sole public location-tree/provenance query with a root and a
zero-based path:

```coq
skylabs.lang.cpp.syntax.source_location.lookup
  source_locations (DRSymbol name) [0; 2; 1]
```

The result is `inr origins` on success or `inl error` for a missing root, an
out-of-bounds child, or an invalid origin/anchor/derivation ID. Success with no
provenance is distinct and returns `inr []`.

### Path order

A path starts at the final semantic value stored at the selected root; `[]`
selects that root. Each index selects a recursive semantic child in constructor
field order. Required node fields contribute one child, present options one,
lists one child per element in source order, and products or the active sum
payload flatten left-to-right. Scalars and container syntax add no levels.
Consequently, for example, `Ebinop op lhs rhs ty` has children
`[lhs; rhs; ty]`, and an `Ecall fn args` has `fn` followed by its arguments.

Paths describe cpp2v's final core IR, not the Clang AST or the printed Rocq
syntax. Erased wrappers do not add a level; their transformed origins can be
retained on the surviving node. Synthesized and unsupported final nodes remain
explicit when they carry semantic structure.

Each returned `source_origin` can distinguish explicit, implicit,
Clang-transformed, cpp2v-synthesized, and inherited provenance. It can contain
independent spelling and expansion ranges, physical byte/line/column points,
presumed `#line` points, nested macro frames, a point of instantiation, a
synthetic anchor, and derivation edges. Range endpoints are optional, so an
invalid or non-contiguous Clang projection is represented rather than guessed.

### Templates, sharing, and limitations

`--no-templates` omits template root events and leaves both template location
maps empty. `--no-sharing` can change ordinary AST text but cannot change
companion bytes or paths: companion semantic values are always inline and path
shape comes only from owned recursive occurrences.

This version intentionally provides no zipper, provenance-aware traversal,
ancestor fallback, or lookup from an isolated AST value. It does not detect a
stale or mismatched AST/companion pair, preserve paths across later semantic
transformations, or attach roots to non-name-keyed translation-unit metadata.
Consumers should retain the generated pair from one cpp2v invocation and use
`lookup` directly.

## Directory layout

Directories `src` and `include` hold the implementation of the `cpp2v`. The
directory `llvm-include` additionally contain extensions of LLVM source code
(see [llvm-include/LICENSE.txt](llvm-include/LICENSE.txt) for the license that
is associated to these files).
