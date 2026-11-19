The template parameter object is unsupported: cpp2v marks references to it
(with its symbol), so only functions using it fail the type check.
  $ check_cpp2v_versions test.cpp 20 2>&1 | grep -m1 -o 'Eunsupported "_Z[A-Za-z0-9_]*"'
  Eunsupported "_ZTAXtl1PLi3EEE"
  [1]
