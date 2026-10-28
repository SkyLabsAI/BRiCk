cpp2v emits a class with a virtual base as unsupported, and Clang's path to a
virtual base skips the classes in between, so BRiCk cannot check a cast to a
virtual base or out of such a class. These casts are emitted as Cunsupported;
the other casts keep their path, and the file type-checks.

  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v

The casts of each declaration, without elaboration so that only the members
the test uses are defined, and with names printed in place.

  $ cpp2v --no-sharing --no-elaborate -vv -o sites.v test.cpp -- -std=c++17 2>&1 | grep 'unsupported cast' | sed 's|<.*/|<|'
  unsupported cast through a class with virtual bases (at <test.cpp:4:8>)
  unsupported cast through a class with virtual bases (at <test.cpp:10:24>)
  unsupported cast through a class with virtual bases (at <test.cpp:15:8>)
  unsupported cast through a class with virtual bases (at <test.cpp:16:8>)
  unsupported cast through a class with virtual bases (at <test.cpp:20:8>)
  unsupported cast through a class with virtual bases (at <test.cpp:21:8>)
  unsupported cast through a class with virtual bases (at <test.cpp:22:8>)
  unsupported cast through a class with virtual bases (at <test.cpp:33:36>)
  unsupported cast through a class with virtual bases (at <test.cpp:33:46, col:64>)
  $ awk -f casts.awk sites.v | sed 's/(Nglobal (Nid \("[^"]*"\)))/\1/g'
  (Dconstructor (Nscoped "D" (Nctor ((Tref (Qconst (Tnamed "D"))) :: nil)))
    (Cunsupported "UncheckedDerivedToBase" (Tref (Qconst (Tnamed "VB"))))
  (Dconstructor (Nscoped "E" (Nctor ((Tref (Qconst (Tnamed "E"))) :: nil)))
    (Cunsupported "DerivedToBase" (Tref (Qconst (Tnamed "VB"))))
  (Dconstructor (Nscoped "M" (Nctor ((Tref (Qconst (Tnamed "M"))) :: nil)))
    (Cunsupported "UncheckedDerivedToBase" (Tref (Qconst (Tnamed "VB"))))
  (Dconstructor (Nscoped "F" (Nctor ((Tref (Qconst (Tnamed "F"))) :: nil)))
    (Cunsupported "UncheckedDerivedToBase" (Tref (Qconst (Tnamed "VB"))))
    (Cderived2base nil (Tref (Qconst (Tnamed "M"))))
  (Dconstructor (Nscoped "L" (Nctor ((Tref (Qconst (Tnamed "L"))) :: nil)))
    (Cunsupported "UncheckedDerivedToBase" (Tref (Qconst (Tnamed "VB"))))
  (Dconstructor (Nscoped "R" (Nctor ((Tref (Qconst (Tnamed "R"))) :: nil)))
    (Cunsupported "UncheckedDerivedToBase" (Tref (Qconst (Tnamed "VB"))))
  (Dconstructor (Nscoped "G" (Nctor ((Tref (Qconst (Tnamed "G"))) :: nil)))
    (Cunsupported "UncheckedDerivedToBase" (Tref (Qconst (Tnamed "VB"))))
    (Cderived2base nil (Tref (Qconst (Tnamed "L"))))
    (Cderived2base nil (Tref (Qconst (Tnamed "R"))))
  (Dconstructor (Nscoped "N" (Nctor ((Tref (Qconst (Tnamed "N"))) :: nil)))
    (Cderived2base nil (Tref (Qconst (Tnamed "NB"))))
  (Dconstructor (Nscoped "P" (Nctor ((Tref (Qconst (Tnamed "P"))) :: nil)))
    (Cderived2base nil (Tref (Qconst (Tnamed "N"))))
  (Dfunction (Nglobal (Nfunction function_qualifiers.N "copy_nonvirtual" nil))
    (Cderived2base ((Tnamed "N") :: nil) (Tref (Tnamed "NB")))
    (Cbase2derived ((Tnamed "N") :: nil) (Tref (Tnamed "P")))
  (Dfunction (Nglobal (Nfunction function_qualifiers.N "convert_mixed" ((Tref (Tnamed "X")) :: nil)))
    (Cunsupported "DerivedToBase" (Tref (Tnamed "NB")))
    (Cunsupported "BaseToDerived" (Tref (Tnamed "X")))
