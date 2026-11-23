"""Compile/run standalone design examples; does not test a BRiCk implementation."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
EXAMPLES = ROOT / "examples"
CC = shlex.split(os.environ.get("CC", "clang"))
CXX = shlex.split(os.environ.get("CXX", "clang++"))


def run(args):
    subprocess.run([str(x) for x in args], check=True)


with tempfile.TemporaryDirectory(prefix="goto-cleanup-") as directory:
    build = Path(directory)
    print("C compiler:", flush=True)
    run(CC + ["--version"])
    print("C++ compiler:", flush=True)
    run(CXX + ["--version"])
    rejected = subprocess.run(
        CXX + ["-x", "c++", "-std=c++17", "-pedantic-errors", "-fsyntax-only",
               str(EXAMPLES / "original.c")], capture_output=True, text=True)
    assert rejected.returncode != 0, "original must reject bypassed initialization in C++"
    assert "initializ" in rejected.stderr.lower(), rejected.stderr
    print("original as C++: expected initialization diagnostic\n" + rejected.stderr,
          flush=True)
    run(CXX + ["-std=c++17", "-pedantic-errors", "-fsyntax-only",
               EXAMPLES / "rejected.cpp"])
    for optimization in ["-O0", "-O2"]:
        run(CC + ["-std=c11", optimization, "-Wall", "-Wextra", "-pedantic-errors", "-c",
                  EXAMPLES / "original.c", "-o", build / "original.o"])
        for source in ["resource_ladder.cpp", "same_scope.cpp", "counterexamples.cpp"]:
            binary = build / (Path(source).stem + optimization)
            args = CXX + ["-std=c++17", optimization, "-Wall", "-Wextra", "-pedantic-errors",
                          EXAMPLES / source]
            if source == "resource_ladder.cpp":
                args += [build / "original.o"]
            print(source, optimization, flush=True)
            run(args + ["-o", binary])
            run([binary])
    generated = build / "growth_generated.cpp"
    run(["python3", ROOT / "growth.py", "--output", generated])
    run(CXX + ["-std=c++17", "-O2", generated, "-o", build / "growth"])
    run([build / "growth"])
print("PASS: native design checks only; no Rocq proof or normalizer was tested.")
