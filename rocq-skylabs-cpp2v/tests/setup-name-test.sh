#
# Copyright (C) 2024 BlueRock Security, Inc.
# All rights reserved.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

# NOTE: dash limitations for CI

scrub() {
	# The comments `(* kind name at loc *)` are useful when
	# writing tests but interfere with CI. Name and loc vary
	# across machines and llvm versions.
	grep -E -hv '^[ 	]+\(\*[^*]*\*\)$' ${1+"$@"} /dev/null
}

name_test_versions() {
	local input base ver output std status
	case $# in
	0|1)
		echo >&2 usage: name_test_versions file.cpp ver ...
		return 1
		;;
	esac

	input="$1"; base="${1%.*}"; shift
	status=0
	for ver in "$@"
	do
		output="${base}_${ver}_name_test.v"
		std="-std=c++${ver}"
		echo "# cpp2v --name-test=${output} ${input} -- ${std}" >&2
		cpp2v "--name-test=${output}" "${input}" -- "${std}" || status=1
		echo "# scrub ${output}" >&2
		scrub "${output}" || status=1
	done
	return $status
}

name_test() {
	case $# in
	1)
		name_test_versions "$1" 17
		;;
	*)
		echo >&2 usage: name_test file.cpp
		return 1
		;;
	esac
}
