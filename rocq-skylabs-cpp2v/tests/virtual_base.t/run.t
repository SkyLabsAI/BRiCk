cpp2v emits a class with a virtual base as unsupported, and Clang's path to a
virtual base skips the classes in between, so BRiCk cannot check a cast to a
virtual base or out of such a class. These casts are emitted as Cunsupported;
the other casts keep their path, and the file type-checks.

  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -o 'Cunsupported "[A-Za-z]*"' test_17_cpp.v | sort | uniq -c
        1 Cunsupported "BaseToDerived"
        2 Cunsupported "DerivedToBase"
       42 Cunsupported "UncheckedDerivedToBase"
  $ grep -o 'C\(derived2base\|base2derived\)' test_17_cpp.v | sort | uniq -c
        1 Cbase2derived
       31 Cderived2base
