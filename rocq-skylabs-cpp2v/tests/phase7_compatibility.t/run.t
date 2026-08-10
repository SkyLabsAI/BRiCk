  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

Clang can defer dependent structured-binding initializers, erase an immediately
invoked lambda while reducing an unresolved callee name, represent an array
whose dependent bound is deduced from its initializer, defer overload
resolution for a direct allocation-function call, and use a dependent array
subscript as an unresolved callee. All five cases retain exact final-core
boundaries and compile in ordinary and companion output.

  $ check_cpp2v_locations_versions fixture.cpp 20
  cpp2v -v -check-types -o fixture_20_cpp.v --locations fixture_20_cpp_locations.v fixture.cpp -- -std=c++20 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_20_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_20_cpp_locations.v
  $ test "$(grep -o 'Eunsupported "BindingDecl"' fixture_20_cpp.v | wc -l)" -eq 2
  $ grep -q 'core.Eunresolved_call (Nunsupported "Elambda")' fixture_20_cpp.v
  $ test "$(grep -o 'Nunsupported "Elambda"' fixture_20_cpp.v | wc -l)" -eq 1
  $ grep -q 'Tunsupported "DependentSizedArray const int\[\]"' fixture_20_cpp.v
  $ grep -q 'core.Nop function_qualifiers.N (OONew false) nil' fixture_20_cpp.v
  $ grep -q 'core.Nop function_qualifiers.N (OONew true) nil' fixture_20_cpp.v
  $ grep -q 'core.Nop function_qualifiers.N (OODelete false) nil' fixture_20_cpp.v
  $ grep -q 'core.Nop function_qualifiers.N (OODelete true) nil' fixture_20_cpp.v
  $ if grep -Eq 'core.Nop function_qualifiers.N (OONew|OODelete) nil' fixture_20_cpp.v; then false; fi
  $ grep -q 'core.Eunresolved_call (Nunsupported "Esubscript")' fixture_20_cpp.v
  $ grep -q 'core.Eunresolved_call (Nunsupported "Eunresolved_binop")' fixture_20_cpp.v
  $ test "$(grep -o 'Nunsupported "Esubscript"' fixture_20_cpp.v | wc -l)" -eq 1
  $ test "$(grep -o 'Nunsupported "Eunresolved_binop"' fixture_20_cpp.v | wc -l)" -eq 1

The dependent Bbind remains explicit, while its unavailable initializer and its
independent type occurrence carry synthesized and inherited provenance. The
erased lambda and both reduced subscript-callee names keep synthesized and
transformed provenance.

  $ rocq c $ROCQC_ARGS check.v
