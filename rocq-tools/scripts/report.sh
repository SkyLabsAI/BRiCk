#!/bin/bash

# Copyright (C) 2023-2024 BlueRock Security, Inc.
#
# This library is free software; you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation; version 2.1.
#
# This library is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
# for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with this library; if not, write to the Free Software Foundation,
# Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 dir1 ... dirN"
  exit 1
fi

handle_glob(){
  GLOB="$1"
  SRC="${GLOB%.glob}.v"
  OUT="$GLOB.stdout"
  ERR="$GLOB.stderr"
  if [[ -f "$ERR" ]]; then
    # Output the contents of stderr.
    cat "$ERR"
  fi
  if [[ -f "$OUT" ]]; then
    # Output a dummy warning if stdout is non-empty.
    echo "File \"$SRC\", line 0, characters 0-0:"
    echo "Warning: Non-empty stdout when building using \"rocq compile\"."
    echo "[non-empty-stdout,dummy]"
  fi
}

for DIR in "$@"; do
  for GLOB in $(find "$DIR" -type f -name '*.glob'); do
    handle_glob "$GLOB"
  done
done
