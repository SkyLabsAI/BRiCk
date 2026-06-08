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

if [[ $# -ne 2 ]]; then
  echo "Usage: $0 nb_jobs dir"
  exit 1
fi

NBJOBS="$1"
DIR="$2"

hint_data_extract(){
  INPUT="$1"
  OUTPUT="${INPUT%.log.json}.hints.csv"
  echo "$INPUT" | rocq-perf.gather-hint-data > "$OUTPUT"
}
export -f hint_data_extract

find "$DIR" -type f -name '*.log.json' \
  | xargs -P "$NBJOBS" -I {} bash -c 'hint_data_extract "$@"' _ {}
