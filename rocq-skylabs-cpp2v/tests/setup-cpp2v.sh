export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"

ROCQC_ARGS="-w -notation-overridden -w -notation-incompatible-prefix"

sayDo() {
    echo "$@"
    eval "$@"
}

check_cpp2v_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        # Avoid spurious spaces if CRAM_CPP2VFLAGS/CRAM_CXXFLAGS are empty
        sayDo "cpp2v -v -check-types -o ${base}_${ver}_cpp.v ${input}${CRAM_CPP2VFLAGS:+ ${CRAM_CPP2VFLAGS}} -- -std=c++${ver}${CRAM_CXXFLAGS:+ ${CRAM_CXXFLAGS}} 2>&1 | sed 's/^ *[0-9]* | //'"
        sayDo "rocq c ${ROCQC_ARGS} ${base}_${ver}_cpp.v"
    done
}

check_cpp2v() {
    check_cpp2v_versions $1 17
}

check_cpp2v_locations_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        ast="${base}_${ver}_cpp.v"
        locations="${base}_${ver}_cpp_locations.v"
        # One cpp2v invocation must produce both halves of the pair.
        sayDo "cpp2v -v -check-types -o ${ast} --locations ${locations} ${input}${CRAM_CPP2VFLAGS:+ ${CRAM_CPP2VFLAGS}} -- -std=c++${ver}${CRAM_CXXFLAGS:+ ${CRAM_CXXFLAGS}} 2>&1 | sed 's/^ *[0-9]* | //'"
        sayDo "rocq c ${ROCQC_ARGS} ${ast}"
        sayDo "rocq c ${ROCQC_ARGS} ${locations}"
    done
}

check_cpp2v_locations() {
    check_cpp2v_locations_versions $1 17
}

# Exercise the lower-level Clang extraction target independently of ToCoq and
# compile its owned Rocq values.
check_cpp2v_source_info_probe() {
    input="$1"
    output="$2"
    shift 2
    args="$*"
    repeat="${output%.v}_repeat.v"
    sayDo "../../build-dune-tests/cpp2v-source-info-probe ${input} --rocq-output ${output} -- ${args}"
    sayDo "../../build-dune-tests/cpp2v-source-info-probe ${input} --rocq-output ${repeat} -- ${args} > ${repeat%.v}.log"
    sayDo "cmp ${output} ${repeat}"
    sayDo "rocq c ${ROCQC_ARGS} ${output}"
    rm -f "${repeat}" "${repeat%.v}.log"
}

check_cpp2v_source_info_probe_versions() {
    input="$1"
    base="${input%.*}"
    shift
    for ver in "$@"
    do
        check_cpp2v_source_info_probe "${input}" "${base}_${ver}_source_values.v" \
            "-std=c++${ver}" ${CRAM_CXXFLAGS}
    done
}

check_cpp2v_templates_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        # Avoid spurious spaces if CRAM_CPP2VFLAGS/CRAM_CXXFLAGS are empty
        sayDo "cpp2v -v -check-types -o ${base}_${ver}_cpp.v --templates ${base}_${ver}_cpp_templates.v ${input}${CRAM_CPP2VFLAGS:+ ${CRAM_CPP2VFLAGS}} -- -std=c++${ver}${CRAM_CXXFLAGS:+ ${CRAM_CXXFLAGS}} 2>&1 | sed 's/^ *[0-9]* | //'"
        sayDo "rocq c ${ROCQC_ARGS} ${base}_${ver}_cpp_templates.v"
        sayDo "rocq c ${ROCQC_ARGS} ${base}_${ver}_cpp.v"
    done
}

check_cpp2v_templates() {
    check_cpp2v_templates_versions $1 17
}
