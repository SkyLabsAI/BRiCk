cpp2v erases a typedef to its underlying type, losing an alignment attribute.
Where Clang's alignof of a type differs from that of the type cpp2v prints,
cpp2v prints Clang's constant instead of an alignof expression; this also
covers reference types and GNU alignof of a variable.

  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:14:32: warning: 'alignof' applied to an expression is a GNU extension
  unsigned long a_var() { return alignof(v); } // GNU extension
                                 ^
  $TESTCASE_ROOT/test.cpp:57:5: warning: passing 1-byte aligned argument to 4-byte aligned parameter 'this' of 'S2' may result in an unaligned pointer access
  US2 g_rec;
      ^
  $TESTCASE_ROOT/test.cpp:66:29: warning: taking address of packed member 'i' of class or structure 'P' may result in an unaligned pointer value
  int *addr_i(P *p) { return &p->i; }
                              ^~~~
  3 warnings generated.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v

  $ grep -o -E 'Dtypedef \(Nglobal \(Nid "(X|u16a)"\)\) [A-Za-z_]+' test_17_cpp.v
  Dtypedef (Nglobal (Nid "X")) Tint
  Dtypedef (Nglobal (Nid "u16a")) Tushort

The function bodies in order (a_over, a_under, a_ref, a_plain, s_over, a_var,
a_inc, a_e8, a_e1), then the two static assertions.

  $ grep -o -E '(Eint [0-9]+%Z|E(alignof|sizeof)[a-z_]* \([^)]*\)) Tulong' test_17_cpp.v
  Eint 16%Z Tulong
  Eint 1%Z Tulong
  Eint 16%Z Tulong
  Ealignof (inl Tint) Tulong
  Esizeof (inl Tint) Tulong
  Eint 16%Z Tulong
  Eint 4%Z Tulong
  Eint 8%Z Tulong
  Eint 1%Z Tulong
  Esizeof (inl Tint) Tulong
  Eint 16%Z Tulong
  Esizeof (inl Tushort) Tulong
  Eint 1%Z Tulong

A field placed below the alignment of its type, by a packed attribute, a
pragma or an under-aligned typedef, has a Trealigned type around its scalar
element type, with the alignment the layout guarantees. The comparison uses
the alignment BRiCk assumes, which for an enumeration is that of its
underlying type: E1 at offset 1 is wrapped, E8 at offset 4 is not.
Under-aligned fields of class type are still unsupported. (The counts
include member expressions, which carry the field's type.) A variable of an
under-aligned typedef type gets the same wrapper (an over-aligned one does
not need it), or an unsupported type when the wrapper cannot express it. A
function with an under-aligned parameter is unsupported.

  $ grep -o -E '\(Q[a-z_]+ \(Trealigned [0-9]+ (\([^()]*\)|[^() ]+)\)\)|\(Tarray \(Trealigned [0-9]+ (\([^()]*\)|[^() ]+)\) [0-9]+\)|\(Trealigned [0-9]+ (\([^()]*\)|[^() ]+)\)' test_17_cpp.v | sort | uniq -c
        3 (Qconst (Trealigned 1 Tshort))
        1 (Tarray (Trealigned 1 Tulonglong) 2)
        1 (Tarray (Trealigned 1 Tushort) 1)
        9 (Trealigned 1 (Tenum n30))
        6 (Trealigned 1 Tint)
       11 (Trealigned 1 Tushort)
        9 (Trealigned 2 Tint)
  $ grep -o -E '"[^"]*not supported"|"under-aligned variable"' test_17_cpp.v
  "under-aligned variable"
  "under-aligned fields of class type are not supported"
  "under-aligned parameters are not supported"
  "under-aligned variable"
  "under-aligned variable"

Clang rejects an array whose element size is not a multiple of the element
alignment, so such a type cannot be an array element.

  $ cpp2v -o array.v array.cpp -- -std=c++17 2>&1 | grep -o 'error: .*'
  error: size of array element of type 'X' (aka 'int') (4 bytes) isn't a multiple of its alignment (16 bytes)
  [1]

A read of a packed field reads its Trealigned object and retypes the value
with a no-op cast, whose rule asks the prover to show the value has the new
type; an assignment used as a statement stores at the Trealigned type. Other
uses (address-of, reference binding, compound assignment, using the value of
an assignment) are unsupported, as Clang types them at the naturally aligned
type.

  $ tr -s ' \n' ' ' < test_17_cpp.v | sed -E 's/ t[0-9]+\)/ t_)/g' | grep -o -E 'Eunsupported "[^"]*under-aligned field"|\(Eassign \(Emember true \(Ecast Cl2r \(Evar "p" t_\)\) \(Field \(field_name.Id "i"\) false \(Trealigned 1 Tint\)\)\) \(Eint 5%Z Tint\) \(Trealigned 1 Tint\)\)|\(Ecast \(Cnoop Tint\) \(Ecast Cl2r \(Emember true \(Ecast Cl2r \(Evar "p" t_\)\) \(Field \(field_name.Id "i"\) false \(Trealigned 1 Tint\)\)\)\)\)' | sort | uniq -c
        1 (Eassign (Emember true (Ecast Cl2r (Evar "p" t_)) (Field (field_name.Id "i") false (Trealigned 1 Tint))) (Eint 5%Z Tint) (Trealigned 1 Tint))
        1 (Ecast (Cnoop Tint) (Ecast Cl2r (Emember true (Ecast Cl2r (Evar "p" t_)) (Field (field_name.Id "i") false (Trealigned 1 Tint)))))
        5 Eunsupported "access to an under-aligned field"
        1 Eunsupported "use of an assignment to an under-aligned field"

BRiCk fixes integer sizes and equates the alignment of integers and pointers
with their size, so cpp2v rejects targets that disagree, such as i386, where
long is 32 bits and long long is 4-byte aligned.

  $ cpp2v -o target.v target.cpp -- -std=c++17 --target=i386-linux-gnu 2>&1 | grep -o 'cpp2v does not support.*'
  cpp2v does not support this target: BRiCk assumes that long has size and alignment 64 bits
  [1]
  $ cpp2v -o target.v target.cpp -- -std=c++17 --target=x86_64-windows-msvc 2>&1 | grep -o 'cpp2v does not support.*'
  cpp2v does not support this target: BRiCk assumes that long has size and alignment 64 bits
  [1]
