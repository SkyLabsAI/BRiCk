Opaque metadata does not broaden support to unions, bases, virtual dispatch,
under-aligned ordinary fields, or dependent primary templates.
Do not synthesize member bodies for these intentionally unsupported records.

  $ cpp2v -check-types -no-elaborate -no-sharing -o test_cpp.v --templates test_templates.v test.cpp -- -target x86_64-linux-gnu -std=c++17
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} test_templates.v
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "BitUnion")) "bitfields are not supported")' test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "WithBase")) "bitfields are not supported")' test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "WithVirtual")) "bitfields are not supported")' test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "WithVirtualBase")) "virtual base classes are not supported")' test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "PackedBits")) "bitfields are not supported")' test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "PackedOffset")) "bitfields are not supported")' test_cpp.v
  $ grep -Fq '(Dunsupported (Nglobal (Nid "PackedPlain")) "under-aligned fields are not supported")' test_cpp.v
  $ grep -c '(Dtemplated_unsupported' test_templates.v
  2
  $ grep -Fq '(Ninst (Nglobal (Nid "DependentBits")) ((Avalue (Eparam "Width")) :: nil)) "bitfields are not supported")' test_templates.v
  $ grep -Fq '(Ninst (Nglobal (Nid "DependentType")) ((Atype (Tparam "T")) :: nil)) "bitfields are not supported")' test_templates.v
  $ grep -F 'Dopaque_record' test_cpp.v test_templates.v
  [1]
