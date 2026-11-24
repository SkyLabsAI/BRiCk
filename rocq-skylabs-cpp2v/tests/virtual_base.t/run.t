cpp2v emits a class with a virtual base (direct or indirect) as a Dvstruct,
which records its non-virtual bases and its virtual bases separately. Clang's
path to a virtual base skips the classes in between, so a cast that takes a
step to a virtual base is emitted as Cunsupported. A cast whose steps all go to
non-virtual bases keeps its path, also out of a class with virtual bases (its
non-virtual bases have static offsets), and the file type-checks.

  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v

Each unsupported cast is logged at its site, so a cast that becomes
unsupported, or stops being so, changes this list. Without elaboration only
the members the test uses are defined.

  $ cpp2v --no-elaborate -vv -o sites.v test.cpp -- -std=c++17 2>&1 | grep 'unsupported cast' | sed 's|<.*/|<|'
  unsupported cast to a virtual base (at <test.cpp:4:8>)
  unsupported cast to a virtual base (at <test.cpp:10:24>)
  unsupported cast to a virtual base (at <test.cpp:15:8>)
  unsupported cast to a virtual base (at <test.cpp:16:8>)
  unsupported cast to a virtual base (at <test.cpp:20:8>)
  unsupported cast to a virtual base (at <test.cpp:21:8>)
  unsupported cast to a virtual base (at <test.cpp:22:8>)

The copy constructors of F and G convert to their virtual base VB, which is
unsupported, and to their non-virtual bases M, L and R, which is not; so do the
conversions of X to and from NB.

  $ grep -o 'Cunsupported "[A-Za-z]*"' sites.v | sort | uniq -c
        1 Cunsupported "DerivedToBase"
        6 Cunsupported "UncheckedDerivedToBase"
  $ grep -o 'C\(derived2base\|base2derived\)' sites.v | sort | uniq -c
        2 Cbase2derived
        7 Cderived2base

Every class above with a virtual base is a Dvstruct, including F and G, whose
virtual base is indirect.

  $ grep -c '(Dvstruct' test_17_cpp.v
  8

An explicit destructor call destroys a complete object, virtual bases
included. BRiCk's destructor for such a class only destroys the non-virtual
part, so the call is unsupported.

  $ cat > dtor.cpp <<EOF
  > struct VB { int v; };
  > struct D : virtual VB { };
  > void f(D &d) { d.~D(); }
  > EOF
  $ cpp2v --no-elaborate -o dtor.v dtor.cpp -- -std=c++17 2>&1 | sed 's|<.*/|<|'
  $ grep -c 'Eunsupported "CXXMemberCallExpr"' dtor.v
  1
