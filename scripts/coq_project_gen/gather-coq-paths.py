#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "sexpdata==1.0.2",
# ]
# ///

#
# Copyright (C) 2025 BlueRock Security, Inc.
# All rights reserved.
import sexpdata
import os.path
import sys
import argparse
import re

def find_key(symbol, obj):
    for x in obj:
        if sexpdata.car(x) == sexpdata.Symbol(symbol):
            return sexpdata.cdr(x)
    return None

def get_symbol(obj):
    return sexpdata.car(obj)

def get_args(file_path, prefix=None):
    raw = open(file_path, 'r').read()
    data = sexpdata.loads(f'({raw})')
    physical_path = os.path.dirname(file_path)
    if physical_path.startswith('./'):
        physical_path = physical_path[2:]
    if prefix:
        physical_path = f'{prefix}/{physical_path}'
    theory = find_key('rocq.theory', data)
    if theory is None:
        return []
    logical_path = find_key('name', theory)
    if logical_path is None:
        return []
    logical_path = get_symbol(logical_path)
    add_sources = not re.search('/elpi$', physical_path)
    return ([f'-Q _build/default/{physical_path}/ {logical_path}'] +
        ([f'-Q {physical_path}/ {logical_path}'] if add_sources else []))

def parse_arguments():
    parser = argparse.ArgumentParser(description="Parse arguments with an option prefix.")

    parser.add_argument("--prefix", type=str, default='',
                        help="The prefix that paths are relative to")

    parser.add_argument("paths", nargs=argparse.REMAINDER,
                        help="All other arguments after the prefix.")

    args = parser.parse_args()
    return args

def main():
    args = parse_arguments()

    for x in args.paths:
        if '.git' in x:
            continue
        for arg in get_args(x, prefix=args.prefix):
            print(arg)

if __name__ == '__main__':
    main()

# Usage: ./support/gather-coq-paths.py `find . -name dune`
