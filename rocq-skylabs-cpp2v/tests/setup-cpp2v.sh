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
