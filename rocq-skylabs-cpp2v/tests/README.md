Using Dune "Cram tests" for Coq
===============================

Quick tutorial
--------------

This folder sets up Dune "Cram tests", which is a neat mechanism for testing
programs by feeding them input, and checking their output and return code. A
Cram test can be added by creating a directory whose name ends with the `.t`
extension, and which contains a file `run.t`.

For example, you can create a Cram test that does not test anything using the
following commands from the directory containing the current `README.md`.
```sh
mkdir -p dummy/my_test.t
touch dummy/my_test.t/run.t
```
You can then run your new test using `dune build @my_test` from anywhere in
the repository. In other words, dune automatically creates an alias for your
test, based on its directory name (without the extension). You can also run
it, along with all other tests, using the following command.
```sh
dune runtest
```

Now, let's make our test fail. To do so, we will edit the `run.t` file, and
have it run some command. Let's change its contents to the following.
```sh
cat > dummy/my_test.t/run.t <<EOF
This is a comment, but the next line (starting with "  $") runs a command.
  $ echo "This is a test!"
EOF
```
If you run `dune build @my_test` again, you'll see the test fails, and you
see a "diff" that explains the reason. The `echo` command has output, but
the test file did not specify any output. Command output is specified using
two-space-indented lines, following the command. So we can "fix" this using
```sh
cat > dummy/my_test.t/run.t <<EOF
This is a comment, but the next line (starting with "  $") runs a command.
  $ echo "This is a test!"
  This is a test
EOF
```
but it seems like we forgot the final `!` in the output, as the output of
`dune build @my_test` shows again.

Instead of editing the file manually, since we have checked that the output
actually produced by the command (showed by the diff) is sensible, we can
instead call `dune promote dummy/my_test.t`. Or, to fixup all examples at
once, you can call the following command.
```sh
dune promote
```

Setting up a test for a Coq file
--------------------------------

To process a Coq file and check the produced output in a Cram test, it is
easiest for the test directory to mimic a dune project. The advantage is
that this will take care of dependencies for us, and put them in the right
place (module some limitations that we can easily circumvent). Note that in
the `dune` file placed next to the current `README.md`, it is specified that
all our tests depend on the `coq-cpp2v` and `coq-cpp2v-bin` packages. Hence,
for instance, the `cpp2v` binary is in `PATH` in all Cram tests.

To create a new Cram test called `new_test`, that (sequentially) runs three
files `test1.v`, `test2.v` and `test3.v`, you will need to put your three
files in a new folder `new_test.t`, and add a `new_test.t/run.t` file with
the following contents.
```sh
  $ . ../setup-project.sh
  $ dune build test1.vo
  $ dune build test2.vo
  $ dune build test3.vo
```
Note that you only need to build the files sequentially if any output is
expected from their compilation. If that is not the case, you can replace
this by a single `dune build` call without parameters.

You can then run `dune build @new_test` to check that the test works, which
it should if compiling the files produces no output. If output is produced,
check that the diff makes sense, and promote the `run.t` file.
```sh
dune promote new_test.t/run.t
```

Source-location maintenance
---------------------------

User-facing location tests must invoke cpp2v once and compile both halves of
the generated pair. Reuse `check_cpp2v_locations` or
`check_cpp2v_locations_versions` from `setup-cpp2v.sh`, then compile a
`check.v` containing exact `lookup` assertions. Keep tests thematic rather
than adding one generated snapshot:

- `location_shape.t` covers final-core path order and arity;
- `location_source.t` covers macros, `#line`, includes, and file kinds;
- `location_roots.t` covers root namespaces, transformations, templates, and
  points of instantiation;
- `location_unsupported_perf.t` covers unsupported/invalid provenance and a
  non-golden scaling smoke; and
- `phase6_locations.t` retains sharing, determinism, template filtering,
  publication, fold-selection, and CLI boundary coverage.

A BRiCk constructor change that adds, removes, or reorders a recursive field is
a location-path ABI change. In the same patch, update the constructor registry
shape, checked factory, `Arena::children` unit expectation, public path
documentation, and every affected production lookup proof. Scalars and
list/option/product/sum wrappers must not gain artificial path levels.

Tests should assert stable semantic relationships and fixture-owned physical
coordinates, not Clang's incidental encodings or diagnostics. Do not add
ancestor fallback, zipper APIs, stale-pair checks, or semantic sharing to the
companion as a test workaround. Run workspace Dune commands from the composed
workspace root.
