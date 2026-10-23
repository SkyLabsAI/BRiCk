# Shared host/Docker execution

`rocq-skylabs-cpp2v` installs two companion tools:

- `cpp2v-toolchain configure` records the selected execution environment.
- `cpp2v-toolchain wrapper` generates a thin executable adapter.
- `cpp2v-run` executes arbitrary commands using that environment.

These tools do not require Rocq, assume an `.exe` output, or hardcode test-framework
or sanitizer environment variables. Repositories choose their image and flags.
The scripts need Bash 3.2 or newer and `sha256sum` or `shasum`; Docker is needed
only when the selected mode actually uses a container.

## Configuration

```sh
cpp2v-toolchain configure --image IMAGE --platform linux/amd64 --opam > cpp-environment
```

Docker is opt-in. `CPP2V_DOCKER_ENABLED` accepts:

- unset or `n`: use host commands without contacting Docker;
- `y`: use the selected container image;
- `if-libstdc++`: use Docker only for arguments containing `-stdlib=libstdc++`.

`CPP2V_DOCKER_IMAGE` overrides `--image`; `CPP2V_DOCKER_USER` overrides the current
UID/GID. `--platform` is optional. `--opam` explicitly requests OPAM environment
initialization inside the image; other images need not have Bash or OPAM.

The generated configuration records a cached image ID for the requested platform
when available, so TU translation, compilation/linking, and execution use the same
image, even if its tag changes afterward. If that platform is not cached, or Docker
cannot inspect platforms, the image reference is retained so the requested variant
can be pulled on first execution. Regenerating the configuration then records its
ID when supported. To pin across builds, supply an immutable image reference.
Docker errors never silently select the host.

The workspace defaults to `DUNE_SOURCEROOT`, or the current directory outside
Dune; `--workspace DIR` overrides it. Workspace and working-directory mounts use
the same absolute paths inside the container. Existing absolute file arguments
are mounted as well. Use repeatable `--mount DIR` for external include trees or
external executables. Symlinked directories are mounted from their physical host
locations at the logical paths used by the command. Relative `--mount` paths are
resolved from the physical working directory used inside the container. The
container command itself is never replaced with a mounted host executable.

## Explicit Dune TU rules

Generate configuration once per consumer, with environment dependencies declared:

```lisp
(rule
 (target cpp-environment)
 (deps
  (universe)
  (env_var CPP2V_DOCKER_ENABLED)
  (env_var CPP2V_DOCKER_IMAGE)
  (env_var CPP2V_DOCKER_USER))
 (action
  (with-stdout-to %{target}
   (run %{bin:cpp2v-toolchain} configure --image IMAGE --opam))))

(rule
 (target source_cpp.v)
 (deps (:input source.cpp))
 (action
  (run %{bin:cpp2v-run}
   --config %{dep:cpp-environment}
   --host-tool %{bin:cpp2v} --container-tool cpp2v
   -- %{input} -o %{target} -- -std=c++20)))
```

The explicit `%{bin:cpp2v}` dependency records the actual host executable without
assuming an `_build/install` symlink or OPAM copy exists. Dune tracks the runner,
configuration, and host tool directly. The configuration rule uses `universe` to
notice image retagging without source changes. Build from the workspace root.

Neither `cpp2v` nor `rocq` is shadowed on PATH. Inline Rocq `cpp.prog` translation
is **not** containerized: it retains its existing host-toolchain behavior even
with `CPP2V_DOCKER_ENABLED=y`. Host inline translations may not match Docker TU
headers. For fully pinned proofs using inline C++, run the whole build in the
pinned image/devcontainer, with these Docker wrappers disabled.

## Compilation and arbitrary commands

A compiler adapter can capture a named host tool when available, without requiring
that compiler to be installed for Docker mode:

```lisp
(rule
 (target cxx-tool)
 (deps (universe) (sandbox none))
 (action
  (progn
   (with-stdout-to %{target}
    (run %{bin:cpp2v-toolchain} wrapper
     --runner %{bin:cpp2v-run} --config %{dep:cpp-environment}
     --host-tool clang++ --container-tool clang++))
   (run chmod +x %{target}))))
```

The generator shell-quotes paths and records hashes of the host tool, runner,
and configuration. `universe` and `sandbox none` ensure recorded absolute paths
come from the current build tree rather than another checkout's shared cache.
Invoke the adapter explicitly, or call the runner directly:

```sh
cpp2v-run --config cpp-environment -- clang++ -c source.cpp -o source.o
cpp2v-run --config cpp-environment -- python3 check.py
cpp2v-run --config cpp-environment --flags-file cxx.flags -- ./tests
```

`--flags-file` selects the runtime in `if-libstdc++` mode using the flags that built
the program, rather than interpreting test arguments as compiler flags. Otherwise
arguments after the command select the selective mode.

Add individual environment variables at the call site:

```lisp
(deps (env_var ASAN_OPTIONS))
(action
 (setenv UBSAN_OPTIONS print_stacktrace=1
  (run %{bin:cpp2v-run} --config %{dep:cpp-environment}
   --env ASAN_OPTIONS --env UBSAN_OPTIONS -- ./tests)))
```

`--env NAME` is repeatable and forwards only variables set in the caller. Native
commands inherit their environment normally. Declare `(env_var NAME)` in Dune
when an external variable influences an action; no external dependency is needed
for a fixed value supplied by `setenv`. Do not forward host `PATH` or
`LD_LIBRARY_PATH` into an image when relying on its toolchain.
