export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"

COQC_ARGS="-w -notation-overridden -w -notation-incompatible-prefix"

check_cpp2v_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        echo "cpp2v -v -check-types -names ${base}_${ver}_cpp_names.v -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'"
        cpp2v -v -check-types -names ${base}_${ver}_cpp_names.v -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'

        echo "coqc ${COQC_ARGS} ${base}_${ver}_cpp_names.v"
        coqc ${COQC_ARGS} "${base}_${ver}_cpp_names.v"

        echo "coqc ${COQC_ARGS} ${base}_${ver}_cpp.v"
        coqc ${COQC_ARGS} "${base}_${ver}_cpp.v"
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

        echo "coqc ${COQC_ARGS} ${base}_${ver}_cpp_templates.v"
        coqc ${COQC_ARGS} "${base}_${ver}_cpp_templates.v"

        echo "coqc ${COQC_ARGS} ${base}_${ver}_cpp.v"
        coqc ${COQC_ARGS} "${base}_${ver}_cpp.v"
    done
}

check_cpp2v_templates() {
    check_cpp2v_templates_versions $1 17
}
