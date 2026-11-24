cpp2v emits a class with a virtual base (direct or indirect) as a Dvstruct,
which records its non-virtual bases and its virtual bases separately.

Clang's path for a conversion to a base starts at its last virtual step and
skips the classes before it. A conversion whose path starts with a virtual step
is a Cderived2vbase: its first step goes to a virtual base of the source class.
A conversion whose steps all go to non-virtual bases is a Cderived2base or
Cbase2derived, also out of a class with virtual bases. The file type-checks.

  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v

No conversion here is unsupported: the copy constructors convert to the
virtual base VB, and those of F and G also to their non-virtual bases M, L and
R; X converts to and from NB. Without elaboration only the members the test
uses are defined.

  $ cpp2v --no-elaborate -vv -o sites.v test.cpp -- -std=c++17 2>&1 | grep 'unsupported cast'
  [1]
  $ grep -o 'C\(derived2base\|base2derived\|derived2vbase\|unsupported\)' sites.v | sort | uniq -c
        2 Cbase2derived
        7 Cderived2base
        7 Cderived2vbase

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
