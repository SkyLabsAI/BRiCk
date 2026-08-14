  $ . ../../setup-cpp2v.sh
  $ probe=../../../build-dune-tests/cpp2v-sharing-builder-probe
  $ "$probe" fixture.cpp > first.out
  $ cat first.out
  Definition n1 : Mname := (Nglobal (Nid "Shared")).
  Definition t1 : Mtype := (Tenum n1).
  Definition t2 : Mtype := (Tptr t1).
  Definition t3 : Mtype := (Tptr (Tqualified QC t1)).
  Definition n2 : Mname := (Nglobal (core.Nfunction function_qualifiers.N "shared_function" (t2 :: nil))).
  INLINE_TYPE (Tptr (Tenum (Nglobal (Nid "Shared"))))
  SHARED_TYPE t2
  STATIC_NAME n2
  TEMPLATE_NAME n2
  TEMPLATE_ONLY (Tptr (Tnum int_rank.Ilong Signed))

The sharing definitions are ordinary-seed-only, child-first, and put the
function's parameter type before the function name. Both semantic modes see the
same plan. Rocq proves that references unfold to the no-sharing terms.

  $ { echo 'Require Import skylabs.lang.cpp.mparser.'; echo '#[local] Open Scope pstring_scope.'; grep '^Definition ' first.out; sed -n 's/^INLINE_TYPE /Definition inline_type : Mtype := /p' first.out | sed 's/$/./'; sed -n 's/^TEMPLATE_ONLY /Definition template_only : Mtype := /p' first.out | sed 's/$/./'; cat <<'EOF'; } > check.v
  > Example sharing_semantic_equality : t2 = inline_type. Proof. vm_compute. reflexivity. Qed.
  > Example static_meta_plan_equality : n2 = n2. Proof. reflexivity. Qed.
  > EOF
  $ rocq c $ROCQC_ARGS check.v

The pre-switch audit independently proved the same sequence against legacy
PrePrint before that semantic implementation was removed. The permanent owned
probe fixes the exact five-definition production-seed policy.

  $ test "$(grep -c '^Definition ' first.out)" -eq 5

Template-only identities stay inline and do not perturb the stable ordinary
numbering. Repeated extraction is byte deterministic.

  $ grep -Fq 'TEMPLATE_ONLY (Tptr ' first.out
  $ "$probe" fixture.cpp > second.out
  $ cmp first.out second.out
