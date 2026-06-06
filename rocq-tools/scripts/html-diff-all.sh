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

if [[ $# -ne 3 ]]; then
  echo "Usage: $0 ref_dir src_dir output_dir"
  exit 1
fi

REF_DIR="$1"
SRC_DIR="$2"
OUT_DIR="$3"

INDEX_FILE="$OUT_DIR/index.csv"

check_removed(){
  FILE="$1"

  if ! grep -q -F "$FILE" "$SRC_DIR/sources.txt"; then
    # File has been removed.
    echo "$FILE,removed" >> "$INDEX_FILE"
  fi
}

handle_file(){
  FILE="$1"
  BASE="${FILE%.v}"

  if grep -q -F "$FILE" "$REF_DIR/sources.txt"; then
    # File also exists in the reference.
    if grep -q -F "$FILE" "$SRC_DIR/no_data.txt"; then
      # File was compiled without performance data.
      if grep -q -F "$FILE" "$REF_DIR/no_data.txt"; then
        # Compiled without performance data also in the reference.
        echo "$FILE,nodata" >> "$INDEX_FILE"
      else
        # Had performance data in the reference.
        echo "$FILE,nomoredata" >> "$INDEX_FILE"
      fi
    else
      if [[ -f "$SRC_DIR/$FILE" ]]; then
        # The file was compiled.
        if [[ -f "$REF_DIR/$FILE" ]]; then
          # The file was also compiled in the reference.
          if grep -q -F "$FILE" "$REF_DIR/no_data.txt"; then
            # Compiled without performance data in the reference.
            echo "$FILE,newdata" >> "$INDEX_FILE"
          else
            # We have performance data on both sides.
            if cmp -s "$REF_DIR/$BASE.json" "$SRC_DIR/$BASE.json" && \
               cmp -s "$REF_DIR/$FILE" "$SRC_DIR/$FILE"; then
              # File has not changed, same performance data.
              echo "$FILE,identical" >> "$INDEX_FILE"
            else
              mkdir -p "$OUT_DIR/$(dirname "$FILE")/"
              rocq-perf.html-diff \
                "$REF_DIR/$FILE" "$REF_DIR/$BASE.json" \
                "$SRC_DIR/$FILE" "$SRC_DIR/$BASE.json" > "$OUT_DIR/$BASE.html"
              if [[ $? -eq 0 ]]; then
                echo "$FILE,diff,$BASE.html" >> "$INDEX_FILE"
              else
                rm -f "$OUT_DIR/$BASE.html"
                echo "$FILE,differror" >> "$INDEX_FILE"
              fi
            fi
          fi
        else
          # The file was not compiled in the reference.
          echo "$FILE,refnotcompiled" >> "$INDEX_FILE"
        fi
      else
        # The file was not compiled
        if [[ -f "$REF_DIR/$FILE" ]]; then
          # The file was compiled in the reference.
          echo "$FILE,srcnotcompiled" >> "$INDEX_FILE"
        else
          # File not compiled on either side.
          echo "$FILE,notcompiled" >> "$INDEX_FILE"
        fi
      fi    
    fi
  else
    # The file is new.
    echo "$FILE,added" >> "$INDEX_FILE"
  fi
}
export -f handle_file
export -f check_removed
export REF_DIR
export SRC_DIR
export OUT_DIR
export INDEX_FILE

if [[ -d "$OUT_DIR" ]]; then
  echo "Directory $OUT_DIR already exists."
  exit 1
fi

mkdir "$OUT_DIR"

cat "$SRC_DIR/sources.txt" | xargs -I {} bash -c 'handle_file "$@"' _ {}
cat "$REF_DIR/sources.txt" | xargs -I {} bash -c 'check_removed "$@"' _ {}

rocq-perf.html-index "$INDEX_FILE" "$OUT_DIR/index.html"
