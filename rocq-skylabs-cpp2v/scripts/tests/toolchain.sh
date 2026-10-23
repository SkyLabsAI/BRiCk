#!/usr/bin/env bash
# Hermetic runner/adapter checks: no compiler, OPAM switch, or Docker daemon.
set -euo pipefail
absolute() { printf '%s/%s\n' "$(cd "$(dirname "$1")" && pwd -P)" "${1##*/}"; }
runner=$(absolute "$1")
factory=$(absolute "$2")
bash=$BASH
env=$(command -v env)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
unset CPP2V_DOCKER_ENABLED CPP2V_DOCKER_IMAGE CPP2V_DOCKER_USER BASH_ENV ENV
export DUNE_SOURCEROOT="$tmp/workspace with spaces"
export ARGV_LOG="$tmp/argv" INSPECT_LOG="$tmp/inspect" OPAM_LOG="$tmp/opam"
export INSPECT_ARGV_LOG="$tmp/inspect-argv"
export MOCK_IMAGE_ID=sha256:first MOCK_IMAGE_PLATFORM=linux/amd64
export MOCK_STATUS=0 MOCK_PLATFORM_INSPECT_STATUS=0
mkdir -p "$tmp/bin" "$DUNE_SOURCEROOT/tu" "$tmp/built tools & quote'"
host="$tmp/built tools & quote'/cpp2v"
cat > "$host" <<'EOF'
#!/usr/bin/env bash
printf '%s\0' "${0##*/}" "$@" > "$ARGV_LOG"
exit "${MOCK_STATUS:-0}"
EOF
cat > "$tmp/bin/docker" <<'EOF'
#!/usr/bin/env bash
if [[ $1 == image ]]; then
    printf 'inspect\n' >> "$INSPECT_LOG"
    printf '%s\0' "$@" > "$INSPECT_ARGV_LOG"
    platform=
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --platform) platform=$2; shift 2 ;;
            *) shift ;;
        esac
    done
    if [[ -n $platform ]]; then
        [[ $MOCK_PLATFORM_INSPECT_STATUS == 0 ]] || exit "$MOCK_PLATFORM_INSPECT_STATUS"
        # Docker can return an uncached descriptor successfully, with no config.
        if [[ $platform == "$MOCK_IMAGE_PLATFORM" ]]; then
            printf '%s\n' "${MOCK_IMAGE_PLATFORM#*/}"
        fi
    else
        printf '%s\n' "$MOCK_IMAGE_ID"
    fi
else
    printf '%s\0' docker "$@" > "$ARGV_LOG"
    exit "${MOCK_STATUS:-0}"
fi
EOF
cat > "$tmp/bin/opam" <<'EOF'
#!/usr/bin/env bash
touch "$OPAM_LOG"
exit 99
EOF
chmod +x "$host" "$tmp/bin/"*
export PATH="$tmp/bin:$PATH"
config="$tmp/config"
adapter="$tmp/adapter"
cd "$DUNE_SOURCEROOT/tu"

expect_status() {
    local expected=$1 actual=0
    shift
    "$@" > "$tmp/stdout" 2> "$tmp/stderr" || actual=$?
    if [[ $actual != "$expected" ]]; then
        cat "$tmp/stderr" >&2
        echo "expected status $expected, got $actual: $*" >&2
        exit 1
    fi
}
expect_not() {
    if "$@"; then echo "unexpected success: $*" >&2; exit 1; fi
}
read_args() {
    argv=()
    local arg
    while IFS= read -r -d '' arg; do argv+=("$arg"); done < "$ARGV_LOG"
}
has_arg() {
    local arg
    for arg in "${argv[@]}"; do if [[ $arg == "$1" ]]; then return 0; fi; done
    return 1
}
make_adapter() {
    "$bash" "$factory" wrapper --runner "$runner" --config "$config" \
        --host-tool "$host" --container-tool cpp2v > "$adapter"
    chmod +x "$adapter"
}

# Native defaults never contact Docker, even with an image override, and use
# the resolved host command without an install symlink or OPAM fallback.
CPP2V_DOCKER_IMAGE=other-image "$bash" "$factory" configure --image default-image > "$config"
test ! -e "$INSPECT_LOG"
make_adapter
test ! -e "$DUNE_SOURCEROOT/_build/install/default/bin/cpp2v"
# shellcheck disable=SC2016 # Literal characters must survive all adapter layers.
args=('input with spaces.cc' '-DVALUE="literal $value"' '')
"$adapter" "${args[@]}"
read_args
printf '%s\0' cpp2v "${args[@]}" > "$tmp/expected"
cmp "$tmp/expected" "$ARGV_LOG"
# TU rules call the runner explicitly, without changing cpp2v on PATH.
expect_status 0 "$bash" "$runner" --config "$config" \
    --host-tool "$host" --container-tool cpp2v -- "${args[@]}"
cmp "$tmp/expected" "$ARGV_LOG"
test ! -e "$OPAM_LOG"
expect_status 23 "$env" MOCK_STATUS=23 "$adapter" "${args[@]}"
expect_status 0 "$env" -u DUNE_SOURCEROOT "$adapter" "${args[@]}"
cp "$adapter" "$tmp/before"
printf '# host implementation changed\n' >> "$host"
make_adapter
expect_not cmp -s "$adapter" "$tmp/before"

# Configuration pins an image ID. Runtime options are explicit and arbitrary,
# not a built-in whitelist of gtest or sanitizer names.
export CPP2V_DOCKER_ENABLED=y
"$bash" "$factory" configure --image test-image --platform linux/amd64 --opam > "$config"
printf '%s\0' image inspect --platform linux/amd64 '--format={{.Architecture}}' sha256:first > "$tmp/expected"
cmp "$tmp/expected" "$INSPECT_ARGV_LOG"
make_adapter
expect_status 0 "$adapter" "${args[@]}"
read_args
has_arg sha256:first
has_arg "$DUNE_SOURCEROOT:$DUNE_SOURCEROOT"
has_arg "$PWD"
has_arg linux/amd64
# shellcheck disable=SC2016 # This is the literal container command.
has_arg 'opam_env=$(opam env); eval "$opam_env"; exec "$@"'
has_arg cpp2v
expect_status 0 "$bash" "$runner" --config "$config" \
    --host-tool "$host" --container-tool cpp2v -- "${args[@]}"
read_args
has_arg cpp2v
expect_not has_arg "$host"
argc=${#argv[@]}
[[ ${argv[argc-1]} == '' && ${argv[argc-2]} == "${args[1]}" ]]
expect_status 0 "$env" CUSTOM_TEST_SETTING='value with spaces' \
    "$bash" "$runner" --config "$config" --env CUSTOM_TEST_SETTING --env NOT_SET_FOR_THIS_TEST \
    -- "$host" "${args[@]}"
read_args
has_arg CUSTOM_TEST_SETTING
expect_not has_arg NOT_SET_FOR_THIS_TEST
expect_not has_arg PATH
expect_status 17 "$env" MOCK_STATUS=17 "$adapter" input.cpp
cp "$adapter" "$tmp/before"
export MOCK_IMAGE_ID=sha256:second
"$bash" "$factory" configure --image test-image --platform linux/amd64 --opam > "$config"
make_adapter
expect_not cmp -s "$adapter" "$tmp/before"
expect_status 0 "$adapter" input.cpp
read_args
has_arg sha256:second

# A cached image for another architecture must not replace a pullable reference.
platform_config="$tmp/platform-config"
"$bash" "$factory" configure --image test-image --platform linux/arm64 > "$platform_config"
expect_status 0 "$bash" "$runner" --config "$platform_config" -- /bin/true
read_args
has_arg test-image
has_arg linux/arm64
expect_not has_arg sha256:second
# Older Docker versions may not support platform-aware inspection at all.
MOCK_PLATFORM_INSPECT_STATUS=125 "$bash" "$factory" configure \
    --image test-image --platform linux/amd64 > "$platform_config"
expect_status 0 "$bash" "$runner" --config "$platform_config" -- /bin/true
read_args
has_arg test-image
has_arg linux/amd64
expect_not has_arg sha256:second
# With no platform requested, ordinary image inspection can still pin an ID.
"$bash" "$factory" configure --image test-image > "$platform_config"
printf '%s\0' image inspect '--format={{.Id}}' test-image > "$tmp/expected"
cmp "$tmp/expected" "$INSPECT_ARGV_LOG"
expect_status 0 "$bash" "$runner" --config "$platform_config" -- /bin/true
read_args
has_arg sha256:second

# No suffix restrictions: arbitrary absolute inputs, commands, and explicit
# include directories outside the workspace are mounted at the same paths.
mkdir "$tmp/external inputs" "$tmp/include tree"
touch "$tmp/external inputs/input.unusual-suffix"
expect_status 0 "$bash" "$runner" --config "$config" --mount "$tmp/include tree" --mount "${host%/*}" \
    -- "$host" "$tmp/external inputs/input.unusual-suffix"
read_args
has_arg "$tmp/external inputs:$tmp/external inputs"
has_arg "$tmp/built tools & quote':$tmp/built tools & quote'"
has_arg "$tmp/include tree:$tmp/include tree"
# Symlink spellings in arguments and explicit mounts must exist in the image.
ln -s "$tmp/external inputs" "$tmp/input alias"
ln -s "$tmp/include tree" "$tmp/include alias"
expect_status 0 "$bash" "$runner" --config "$config" \
    --mount "$tmp/include alias" --mount "$tmp/include tree" \
    -- "$host" "$tmp/input alias/input.unusual-suffix" "$tmp/external inputs/input.unusual-suffix"
read_args
has_arg "$tmp/external inputs:$tmp/input alias"
has_arg "$tmp/external inputs:$tmp/external inputs"
has_arg "$tmp/include tree:$tmp/include alias"
has_arg "$tmp/include tree:$tmp/include tree"
has_arg "$tmp/input alias/input.unusual-suffix"
# Relative --mount values are anchored to the physical container working dir.
ln -s "$DUNE_SOURCEROOT/tu" "$tmp/tu alias"
(
    cd "$tmp/tu alias"
    expect_status 0 "$bash" "$runner" --config "$config" --mount '../../include alias' \
        -- /bin/true
)
read_args
has_arg "$tmp/include tree:$tmp/include alias"
expect_status 0 "$bash" "$runner" --config "$config" -- /bin/sh -c true
read_args
expect_not has_arg /bin:/bin
# A compiler need not exist on the host for a Docker-backed build.
"$bash" "$factory" wrapper --runner "$runner" --config "$config" \
    --host-tool not-installed-cxx-for-this-test --container-tool clang++ > "$adapter"
chmod +x "$adapter"
expect_status 0 "$adapter" -c input.cpp -o output.o
read_args
has_arg clang++

# Selective mode uses compilation flags for runtime commands, not test arguments.
export CPP2V_DOCKER_ENABLED=if-libstdc++
"$bash" "$factory" configure --image test-image > "$config"
make_adapter
expect_status 0 "$adapter" input.cpp
read_args
[[ ${argv[0]} == cpp2v ]]
expect_status 0 "$adapter" input.cpp -stdlib=libstdc++
read_args
[[ ${argv[0]} == docker ]]
printf '%s\n' -std=c++20 -stdlib=libstdc++ > "$tmp/flags"
expect_status 0 "$bash" "$runner" --config "$config" --flags-file "$tmp/flags" -- "$host" -stdlib=libc++
read_args
[[ ${argv[0]} == docker ]]
printf '%s\n' -std=c++20 -stdlib=libc++ > "$tmp/flags"
expect_status 0 "$bash" "$runner" --config "$config" --flags-file "$tmp/flags" -- "$host" -stdlib=libstdc++
read_args
[[ ${argv[0]} == cpp2v ]]
# Executable lookup must ignore shell builtins with the same name.
"$bash" "$factory" wrapper --runner "$runner" --config "$config" \
    --host-tool true --container-tool true > "$adapter"
chmod +x "$adapter"
expect_status 0 "$adapter"
expect_status 2 "$env" CPP2V_DOCKER_ENABLED=yes "$bash" "$factory" configure
expect_status 2 "$bash" "$runner" --config "$tmp/missing" -- "$host"
expect_status 2 "$bash" "$runner" --config "$config" --env 'INVALID-NAME' -- "$host"
