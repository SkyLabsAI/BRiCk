  $ . ../../setup-cpp2v.sh
  $ cpp2v -v -o test_17_cpp.v --no-elaborate test.cpp -- -std=c++17 2>&1 | grep "printTemplateParam" | head -n 4 || true
