Opaque records carry Clang layout and destructor metadata, not invented fields.
Pin the target so these size/alignment expectations do not depend on the host.

  $ cpp2v -check-types -no-sharing -o test_cpp.v --templates test_templates.v test.cpp -- -target x86_64-linux-gnu -std=c++17
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} test_templates.v
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} test_cpp.v
  $ grep -c '(Dopaque_record ' test_cpp.v
  5
  $ grep -Fq '(Build_OpaqueRecord (Nscoped (Nglobal (Nid "Bits")) Ndtor) true 4 4)' test_cpp.v
  $ grep -Fq '(Build_OpaqueRecord (Nscoped (Nglobal (Nid "SplitBits")) Ndtor) true 8 4)' test_cpp.v
  $ grep -Fq '(Build_OpaqueRecord (Nscoped (Nglobal (Nid "Nontrivial")) Ndtor) false 16 16)' test_cpp.v
  $ grep -Fq '(Build_OpaqueRecord (Nscoped (Nglobal (Nid "WithMember")) Ndtor) false 32 16)' test_cpp.v
  $ grep -Fq '(Ddestructor (Nscoped (Nglobal (Nid "Nontrivial")) Ndtor)' test_cpp.v
  $ grep -Fq '(Dtype (Nglobal (Nid "Forward")))' test_cpp.v
  $ grep -E 'Build_(Struct|Union)|mkMember|Build_LayoutInfo' test_cpp.v
  [1]

The dependent primary stays unsupported; the instantiated class has concrete
layout metadata and retains its template-instantiation link.

  $ grep -c '(Dtemplated_unsupported' test_templates.v
  1
  $ grep -Fq '(Ninst (Nglobal (Nid "SizedBits")) ((Avalue (Eparam "Width")) :: nil)) "bitfields are not supported")' test_templates.v
  $ grep -F '(Dopaque_record ' test_cpp.v | grep -q 'SizedBits'
  $ grep -F 'Build_OpaqueRecord ' test_cpp.v | grep 'SizedBits' | grep -q 'true 4 4)'
  $ grep -A 4 -F '(Dinstantiation' test_templates.v | grep -q 'SizedBits'

Calls and by-value signatures remain available without exporting field access.

  $ grep -Fq '(Build_Func (Tnamed (Nglobal (Nid "Bits")))' test_cpp.v
  $ grep -Fq '(Build_Func (Tnamed (Nglobal (Nid "Nontrivial")))' test_cpp.v
  $ grep -Fq '(Ecall' test_cpp.v
  $ grep -Fq '(Emember_call ' test_cpp.v
  $ grep -E '\(Field \(field_name.Id "(low|high|bits)"' test_cpp.v
  [1]
