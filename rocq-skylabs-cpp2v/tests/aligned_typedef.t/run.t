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
function with an under-aligned parameter is unsupported. E stands for the
enumeration type, which older Clangs print through a shared type name.

  $ grep -o -E '\(Q[a-z_]+ \(Trealigned [0-9]+ (\([^()]*\)|[^() ]+)\)\)|\(Tarray \(Trealigned [0-9]+ (\([^()]*\)|[^() ]+)\) [0-9]+\)|\(Trealigned [0-9]+ (\([^()]*\)|[^() ]+)\)' test_17_cpp.v | sed -E 's/\(Tenum n[0-9]+\)/E/; s/ t[0-9]+\)/ E)/' | sort | uniq -c
        3 (Qconst (Trealigned 1 Tshort))
        1 (Tarray (Trealigned 1 Tulonglong) 2)
        1 (Tarray (Trealigned 1 Tushort) 1)
        9 (Trealigned 1 E)
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

An aligned allocation or deallocation function receives Clang's alignment of
the allocated type, which BRiCk would compute from the erased type, so a new
or delete of a type with an alignment attribute that needs one is
unsupported; an ordinary new is unchanged.

  $ tr -s ' \n' ' ' < test_17_cpp.v | grep -o -E 'Eunsupported "CXX(New|Delete)Expr"|Enew \(' | sort | uniq -c
        1 Enew (
        1 Eunsupported "CXXDeleteExpr"
        1 Eunsupported "CXXNewExpr"

BRiCk fixes integer sizes and equates the alignment of integers and pointers
with their size, so cpp2v rejects targets that disagree, such as i386, where
long is 32 bits and long long is 4-byte aligned.

  $ cpp2v -o target.v target.cpp -- -std=c++17 --target=i386-linux-gnu 2>&1 | grep -o 'cpp2v does not support.*'
  cpp2v does not support this target: BRiCk assumes that long has size and alignment 64 bits
  [1]
  $ cpp2v -o target.v target.cpp -- -std=c++17 --target=x86_64-windows-msvc 2>&1 | grep -o 'cpp2v does not support.*'
  cpp2v does not support this target: BRiCk assumes that long has size and alignment 64 bits
  [1]

Clang loads and stores through a pointer or reference to an over-aligned type
with that type's alignment, and its optimizer relies on it (with
X32 *p = q, it folds the test of whether p is 32-aligned to true), while
BRiCk, given the erased type, would only require q to be int-aligned. Clang
takes that alignment from a typedef attribute even for arrays and incomplete
types, through implicit derived-to-base conversions, and from the declaration
a variable is accessed through. So these are unsupported, in source order:
the accesses in deref_over, index_over, store_over (the assignment) and
arrow_over, the builtin call in copy_over, the access in arr_over, the
builtin call in void_over, the accesses in redecl_over, extern_over and
gnu_over, the member access in base_over, the call in vcall_over, the use of
the captured parameter in capture_over, the access in weak_over, the
conversion in vbase_over and the delete in delete_over. The accesses after
them are supported: Clang allocates variables (defined at their declared
alignment) and temporaries, and lays out records, and BRiCk takes record
alignment from Clang. C++ requires every definition of a variable declared
with alignas to repeat it, so an extern alignas declaration is trusted.

  $ check_cpp2v over.cpp
  cpp2v -v -check-types -o over_17_cpp.v over.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix over_17_cpp.v
  $ tr -s ' \n' ' ' < over_17_cpp.v | grep -o -E 'Eunsupported "[^"]*"'
  Eunsupported "UnaryOperator"
  Eunsupported "ArraySubscriptExpr"
  Eunsupported "BinaryOperator"
  Eunsupported "MemberExpr"
  Eunsupported "CallExpr"
  Eunsupported "ParenExpr"
  Eunsupported "CallExpr"
  Eunsupported "DeclRefExpr"
  Eunsupported "DeclRefExpr"
  Eunsupported "DeclRefExpr"
  Eunsupported "MemberExpr"
  Eunsupported "CXXMemberCallExpr"
  Eunsupported "MemberExpr"
  Eunsupported "DeclRefExpr"
  Eunsupported "ImplicitCastExpr"
  Eunsupported "CXXDeleteExpr"

An alignment attribute on a typedef can also lower the alignment, below the
alignment BRiCk assumes for the erased type. Clang allocates temporaries of
such a type at the typedef's alignment, so they are unsupported (also for
scalars, where Clang happens to use the natural alignment), and so are
class and array prvalues of such a type, which Clang initializes in a slot at
the typedef's alignment when their context provides none (e.g. when they are
discarded, with no MaterializeTemporaryExpr). Without an alignment argument,
new only guarantees the default new alignment, so a plain new or delete of
such a type whose erased type needs more is unsupported.

  $ check_cpp2v under.cpp
  cpp2v -v -check-types -o under_17_cpp.v under.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/under.cpp:18:39: warning: passing 1-byte aligned argument to 32-byte aligned parameter 'this' of 'S' may result in an unaligned pointer access
  unsigned long temp_rec() { return low(U{7}); }
                                        ^
  $TESTCASE_ROOT/under.cpp:20:30: warning: passing 1-byte aligned argument to 4-byte aligned parameter 1 of 'take' may result in an unaligned pointer access
  int temp_int() { return take(I1(5)); }
                               ^
  $TESTCASE_ROOT/under.cpp:21:27: warning: passing 1-byte aligned argument to 32-byte aligned parameter 'this' of 'S' may result in an unaligned pointer access
  U *new_rec() { return new U; }
                            ^
  $TESTCASE_ROOT/under.cpp:27:23: warning: passing 1-byte aligned argument to 32-byte aligned parameter 'this' of 'S' may result in an unaligned pointer access
  void discard_ctor() { U(); }
                        ^
  $TESTCASE_ROOT/under.cpp:28:31: warning: passing 1-byte aligned argument to 32-byte aligned parameter 'this' of 'S' may result in an unaligned pointer access
  void discard_comma() { (void)(U(), 0); }
                                ^
  5 warnings generated.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix under_17_cpp.v
  $ tr -s ' \n' ' ' < under_17_cpp.v | grep -o -E 'Eunsupported "[^"]*"'
  Eunsupported "MaterializeTemporaryExpr"
  Eunsupported "MaterializeTemporaryExpr"
  Eunsupported "MaterializeTemporaryExpr"
  Eunsupported "CXXNewExpr"
  Eunsupported "CXXDeleteExpr"
  Eunsupported "CallExpr"
  Eunsupported "CXXTemporaryObjectExpr"
  Eunsupported "CXXTemporaryObjectExpr"
  Eunsupported "ConditionalOperator"

Every way to pack a record goes through Clang's layout, so they all give the
same wrappers: the attribute on one field, the C++11 attribute spelling, a
pragma without push (reset by an empty pragma), a member's alignas capped by
a pragma, a packed array field, and the command-line flag. A packed field of
class type is unsupported, while its own type is laid out normally. The
fields in order, with their types and offsets in bits:

  $ cpp2v -o ways.v ways.cpp -- -std=c++17 2>&1 | grep -o 'error: .*'
  [1]
  $ grep -o -E 'mkMember \(field_name.Id "[a-z]+"\) (\([^()]*(\([^()]*\))?[^()]*\)|T[a-z]+) false None|Build_LayoutInfo [0-9]+|Dunsupported n[0-9]+ "[^"]*"' ways.v | sed -E 's/Dunsupported n[0-9]+/Dunsupported/'
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "i") (Trealigned 1 Tint) false None
  Build_LayoutInfo 8
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "i") (Trealigned 1 Tint) false None
  Build_LayoutInfo 8
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "i") (Trealigned 1 Tint) false None
  Build_LayoutInfo 8
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "i") Tint false None
  Build_LayoutInfo 32
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "l") (Trealigned 2 Tlong) false None
  Build_LayoutInfo 16
  mkMember (field_name.Id "i") (Trealigned 2 Tint) false None
  Build_LayoutInfo 80
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "a") (Tarray (Trealigned 1 Tshort) 3) false None
  Build_LayoutInfo 8
  Dunsupported "under-aligned fields of class type are not supported"
  mkMember (field_name.Id "d") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "j") Tint false None
  Build_LayoutInfo 32

  $ cpp2v -o flag.v flag.cpp -- -std=c++17 -fpack-struct=1 2>&1 | grep -o 'error: .*'
  [1]
  $ grep -o -E 'mkMember \(field_name.Id "[a-z]+"\) (\([^()]*(\([^()]*\))?[^()]*\)|T[a-z]+) false None|Build_LayoutInfo [0-9]+' flag.v
  mkMember (field_name.Id "c") Tchar false None
  Build_LayoutInfo 0
  mkMember (field_name.Id "i") (Trealigned 1 Tint) false None
  Build_LayoutInfo 8
