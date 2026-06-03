export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"

ROCQC_ARGS="-w -notation-overridden -w -notation-incompatible-prefix"

check_cpp2v_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        echo "cpp2v -v -check-types -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'"
        cpp2v -v -check-types -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'

        echo "rocq c ${ROCQC_ARGS} ${base}_${ver}_cpp.v"
        rocq c ${ROCQC_ARGS} "${base}_${ver}_cpp.v"
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
        echo "cpp2v -v -check-types -o ${base}_${ver}_cpp.v --templates ${base}_${ver}_cpp_templates.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'"
        cpp2v -v -check-types -o ${base}_${ver}_cpp.v --templates ${base}_${ver}_cpp_templates.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'

        echo "rocq c ${ROCQC_ARGS} ${base}_${ver}_cpp_templates.v"
        rocq c ${ROCQC_ARGS} "${base}_${ver}_cpp_templates.v"

        echo "rocq c ${ROCQC_ARGS} ${base}_${ver}_cpp.v"
        rocq c ${ROCQC_ARGS} "${base}_${ver}_cpp.v"
    done
}

check_cpp2v_templates() {
    check_cpp2v_templates_versions $1 17
}
