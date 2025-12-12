#!/usr/bin/env -S bash -e
##
## Copyright (c) 2023-2025 BlueRock Security, Inc.
## All rights reserved.
##

# Some logic below assumes all paths end in `/`.
mappings=(
  "fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest"
)
# TODO: change cram test setup to generate dune projects in _source_ folder, and
# delete the entry above.

# Options related to warnings.
cat << "EOF"
# AUTO-GENERATED CONTENT, EDIT `gen-_CoqProject-dune.sh` INSTEAD

# Avoid warnings about entries in this _CoqProject
-arg -w -arg -cannot-open-path
EOF

if [ -f coq.flags ]; then
  cat coq.flags
fi

# Add -I option for ocamlfind-based loading of plugins.
echo
echo "# Plugin directory."
echo "-I _build/install/default/lib"

# Add -Q options for mapping directories to logical paths.
# Note we need both:
# - the mapping for the ".v" files (to get a correct mapping when editing,
#   see https://bedrocksystems.atlassian.net/browse/FM-3366),
# - the mapping for the compiled ".vo" files under "_build/default".
echo
echo "# Specified logical paths for directories (for .v and .vo files)."

list_dune_files () {
  find . \
    \( -name _build -o -name .git \) -prune -false \
    -o \
    -name dune \( -type f -o -type l \) -print \
    | sort
}

script_path=`(cd \`dirname $0\`; pwd)`
${script_path}/gather-coq-paths.py `list_dune_files`

for mapping in "${mappings[@]}"; do
  directory=$(echo $mapping | awk '{print $1}')
  [ -d "$directory" ] || continue

  # Avoid mapping `.elpi` files twice to avoid warnings
  if ! echo $directory | grep -q "/elpi/$"; then
    echo "-Q $mapping"
  fi
  echo "-Q _build/default/$mapping"
done
