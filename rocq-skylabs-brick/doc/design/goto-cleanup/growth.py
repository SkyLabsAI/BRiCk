from pathlib import Path
import argparse


def original(n):
    body = ["int x = 0;"]
    for i in range(n):
        body += [f"if (bits & (1u << {i})) goto L{i};", "++x;", f"L{i}:;"]
    return "\n".join(body + ["return x;"])


def expanded(i, n):
    if i == n:
        return "return x;"
    suffix = expanded(i + 1, n)
    return f"if (bits & (1u << {i})) {{\n{suffix}\n}}\n++x;\n{suffix}"


for n in [1, 2, 4, 8, 12]:
    tree = expanded(0, n)
    print(f"stages={n} source_return_count=1 expanded_return_count={tree.count('return x;')} expanded_bytes={len(tree)}")

n = 8
source = "#include <cassert>\n#include <iostream>\n"
source += f"int original(unsigned bits) {{\n{original(n)}\n}}\n"
source += f"int expanded(unsigned bits) {{\nint x = 0;\n{expanded(0, n)}\n}}\n"
source += f"int main() {{ for (unsigned i = 0; i < {1 << n}; ++i) assert(original(i) == expanded(i)); std::cout << \"8 stages: all 256 inputs agree\\n\"; }}\n"
parser = argparse.ArgumentParser(description="Exponential recursive goto expansion")
parser.add_argument("--output", required=True, type=Path)
args = parser.parse_args()
args.output.write_text(source)
