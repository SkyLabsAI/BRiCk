#!/usr/bin/env bash
# Exercise Cram helpers without a compiler, Rocq installation, or Docker daemon.
set -euo pipefail
absolute() { printf '%s/%s\n' "$(cd "$(dirname "$1")" && pwd -P)" "${1##*/}"; }
runner=$(absolute "$1")
factory=$(absolute "$2")
# shellcheck source=/dev/null
source "$(absolute "$3")"
# shellcheck source=/dev/null
source "$(absolute "$4")"
bash=$BASH
tmp=$(cd "$(mktemp -d)" && pwd -P)
trap 'rm -rf "$tmp"' EXIT
unset CPP2V_DOCKER_ENABLED CPP2V_DOCKER_IMAGE CPP2V_DOCKER_USER BASH_ENV ENV
export DUNE_SOURCEROOT="$tmp/workspace with spaces"
export ARGV_LOG="$tmp/argv" MOCK_STATUS=0
mkdir -p "$DUNE_SOURCEROOT" "$tmp/bin" "$tmp/host tools & quote'"
host="$tmp/host tools & quote'/cpp2v"
cat > "$host" <<'EOF'
#!/usr/bin/env bash
if [[ ${0##*/} == docker && ${1-} == image ]]; then
    printf 'sha256:cram\n'
    exit 0
fi
printf '%s\0' "${0##*/}" "$@" > "$ARGV_LOG"
for arg in "$@"; do
    case "$arg" in
        --name-test=*) printf 'name-test output\n' > "${arg#*=}" ;;
    esac
done
exit "$MOCK_STATUS"
EOF
cp "$host" "$tmp/bin/docker"
printf '#!/usr/bin/env bash\nexit 98\n' > "$tmp/bin/cpp2v"
printf '#!/usr/bin/env bash\nexit 0\n' > "$tmp/bin/rocq"
chmod +x "$host" "$tmp/bin/"*
export PATH="$tmp/bin:$PATH"
cd "$DUNE_SOURCEROOT"

read_args() {
    argv=()
    local arg
    while IFS= read -r -d '' arg; do argv+=("$arg"); done < "$ARGV_LOG"
}
require_arg() {
    local arg
    for arg in "${argv[@]}"; do if [[ $arg == "$1" ]]; then return; fi; done
    echo "missing argument: $1" >&2
    exit 1
}

for mode in n y; do
    CPP2V_DOCKER_ENABLED="$mode" "$bash" "$factory" configure \
        --image test-image --opam > "$tmp/config"
    {
        printf 'cpp2v_command() (\n'
        "$bash" "$factory" wrapper --runner "$runner" --config "$tmp/config" \
            --host-tool "$host" --container-tool cpp2v
        printf ')\n'
    } > "$tmp/command.sh"
    # shellcheck source=/dev/null
    source "$tmp/command.sh"
    # Runtime environment changes must not override the recorded selection.
    if [[ $mode == n ]]; then export CPP2V_DOCKER_ENABLED=y
    else export CPP2V_DOCKER_ENABLED=n; fi
    CRAM_CPP2VFLAGS=--no-elaborate CRAM_CXXFLAGS='-DNAME="value with spaces"' \
        check_cpp2v_versions input.cpp 17 20 > "$tmp/stdout"
    read_args
    if [[ $mode == n ]]; then [[ ${argv[0]} == cpp2v ]]
    else [[ ${argv[0]} == docker ]]; require_arg sha256:cram; fi
    require_arg --no-elaborate
    require_arg '-DNAME=value with spaces'
    require_arg -std=c++20
    require_arg input_20_cpp.v
    grep -Fx 'cpp2v -v -check-types -o input_17_cpp.v input.cpp --no-elaborate -- -std=c++17 -DNAME="value with spaces" 2>&1 | sed '\''s/^ *[0-9]* | //'\' "$tmp/stdout" > /dev/null
    check_cpp2v_templates input.cpp > "$tmp/stdout"
    read_args
    require_arg --templates
    require_arg input_17_cpp_templates.v
    name_test input.cpp > "$tmp/stdout" 2> "$tmp/stderr"
    read_args
    require_arg --name-test=input_17_name_test.v
    grep -Fx 'name-test output' "$tmp/stdout" > /dev/null
    # The generated function must preserve the backend's exit status, without
    # replacing the parent shell or falling back to the decoy cpp2v on PATH.
    status=0
    MOCK_STATUS=37 cpp2v_command input.cpp || status=$?
    [[ $status == 37 ]]
    [[ $(type -t cpp2v) == file && $(command -v cpp2v) == "$tmp/bin/cpp2v" ]]
done
