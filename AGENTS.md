# Repository Guide

This repository hosts a collection of Rocq (Coq) packages as well as Rocq-related tools.

## Rocq Style

Follow the conventions in [ROCQ_STYLE.md](ROCQ_STYLE.md).

## OCaml Style

Always use `dune b @fmt` to re-format OCaml code according to the coding convention.

## Using dune

You can **NOT** run two instances of `dune` in parallel. Run them sequentially or pass multiple arguments to `dune` in order to build multiple targets.
