Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog module
  abi Little
  defns (parser.Dtype "align_val_t") (parser.Dtypedef "xx" (Tnamed "align_val_t")).

Print module.
