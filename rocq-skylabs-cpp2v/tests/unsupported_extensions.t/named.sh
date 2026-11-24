# Named loops (C2y N3355) exist from clang 22 (`-fnamed-loops`). Check that
# `break outer;` and `continue outer;` print as [Sunsupported] and that the
# plain `break` of [plain_break] stays [Sbreak]; before clang 22 the flag is
# rejected and there is nothing to check.
mkdir -p named
cpp2v -o named/named_cpp.v named.cpp -- -std=c++23 -Xclang -fnamed-loops \
  > named/cpp2v.log 2>&1
if grep -q "unknown argument: '-fnamed-loops'" named/cpp2v.log; then
  echo "named loops: ok"
  exit 0
fi
nb=$(grep -o 'Sunsupported "named break' named/named_cpp.v | wc -l | tr -d ' ')
nc=$(grep -o 'Sunsupported "named continue' named/named_cpp.v | wc -l | tr -d ' ')
pb=$(grep -o 'Sbreak' named/named_cpp.v | wc -l | tr -d ' ')
if [ "$nb" = 1 ] && [ "$nc" = 1 ] && [ "$pb" = 1 ]; then
  echo "named loops: ok"
else
  echo "named break: $nb, named continue: $nc, Sbreak: $pb"
  cat named/cpp2v.log
fi
