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
cpp2v-toolchain configure --default-image IMAGE --platform linux/amd64 --opam > cpp-environment
```

Docker is opt-in. `CPP2V_DOCKER_ENABLED` accepts:

- unset or `n`: use host commands without contacting Docker;
- `y`: use the selected container image.

The selected mode applies to every command; compiler flags do not affect it.

Image selection uses this precedence, independent of option order:

1. `--image IMAGE`: an explicit command-line selection.
2. `CPP2V_DOCKER_IMAGE`: the caller's environment override.
3. `--default-image IMAGE`: the consumer's fallback.

Repository Dune rules pass `--default-image` so callers can override the image
without editing build rules. Use `--image` to force a selection even when
`CPP2V_DOCKER_IMAGE` is set.

`CPP2V_DOCKER_USER` overrides the current UID/GID. `--platform` is optional.
`--opam` explicitly requests OPAM environment initialization inside the image;
other images need not have Bash or OPAM.

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
   (run %{bin:cpp2v-toolchain} configure --default-image IMAGE --opam))))

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

Neither `cpp2v` nor `rocq` is shadowed on PATH. Unannotated inline Rocq
`cpp.prog` quotations retain their existing host-toolchain behavior, even with
`CPP2V_DOCKER_ENABLED=y`. Opt them into the selected environment explicitly as
shown below.

## Opt-in inline Rocq quotations

`rocq-skylabs-brick-cpp-prog` provides one shared `cpp2v_inline` command. It
accepts a configuration path followed by the ordinary cpp2v arguments and
executes `cpp2v-run`. Each quotation can select a configuration declared as a
named Rocq extra dependency:

```coq
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
From MyProject Extra Dependency "cpp_environment" as cpp_environment.

#[environment="cpp_environment"]
cpp.prog source flags "-std=c++20" prog cpp:{{
  #include <vector>
  void test() { std::vector<int> v; }
}}.
```

The `environment` attribute names the configuration's extra dependency, not a
filename, PATH command, or choice of native compiler. It is
supported only on inline quotations, not `cpp.prog ... defns ...`. Without it,
the old native invocation is unchanged. With it, mode `n` uses the recorded
native translator and mode `y` uses Docker. Unknown dependency names, invalid
configurations, missing tools, and Docker errors never silently select a
different backend. Existing compiler flags and other quotation attributes are
preserved.

Put the configuration in a Rocq theory's logical directory. If it is generated,
produce an otherwise empty `.v` dependency anchor in the same rule so Dune builds
it **before** `rocq dep` scans the theory. For an existing configuration in the
parent directory, use this once in the theory's `dune` file:

```lisp
(rule
 (targets cpp_environment cpp_environment_dependency.v)
 (deps (:config ../cpp_environment))
 (action
  (progn
   (copy %{config} cpp_environment)
   (write-file cpp_environment_dependency.v
    "(* Builds the configuration before rocq dep. *)\n"))))
```

Keep the anchor included in the theory's modules (`:standard` does this). Other
theories can share the same resource by listing its owning theory among their
`theories` dependencies and using its logical name in `From ... Extra Dependency`.
No consumer-specific inline command or PATH adapter is needed. Editors use the
same declarations after Dune builds the generated dependencies.

The extra dependency makes the configuration, including its selected image ID,
a dependency of that `.vo`. The plugin's imported version modules fingerprint
the native translator, runner, and adapter generator, without making shared
Rocq caches depend on checkout-specific command paths. Changes therefore
invalidate inline proofs even when their C++ program is not a standalone TU.
The command is installed as a Rocq resource. If its recorded build paths no
longer exist or have changed, it accepts installed
tools from PATH only when they are byte-identical to the recorded tools.

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
`wrapper --config-from-argument` generates a shared adapter whose first argument
is the configuration, rather than capturing `--config` at generation time. The
two options are mutually exclusive. This form requires an executable host tool
and verifies the recorded runner/native tool identities on invocation, including
when relocating an installed adapter. The inline Rocq command uses this form;
its imported version fingerprint tracks the shared adapter while each quotation
tracks its own configuration.

Invoke the adapter explicitly, or call the runner directly:

```sh
cpp2v-run --config cpp-environment -- clang++ -c source.cpp -o source.o
cpp2v-run --config cpp-environment -- python3 check.py
cpp2v-run --config cpp-environment -- ./tests
```

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
