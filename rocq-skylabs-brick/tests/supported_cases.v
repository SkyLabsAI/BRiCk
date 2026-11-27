(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.syntax.supported.

(** * [supported.report]: false positives and false negatives

    One minimal case per kind of gap the report checks.
    [supported_report.v] covers each status; this file pins down the verdict
    on code whose verdict used to be wrong. A root that resolves to a symbol
    that [cpp.prog] dropped, by its printed name or up to its unsupported
    parts, is "unsupported"; a root that only resembles one, such as
    [long_double_ptr(long double&)], stays "missing". *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu -Wno-vla-cxx-extension" prog cpp:{{
// no rule for [va_arg].
int va(__builtin_va_list ap) { return __builtin_va_arg(ap, int); }

// thread-local storage (cpp2v prints uses as [Eunsupported]).
thread_local int tls;
int get_tls() { return tls; }

// only [seq_cst] atomics with a rule are supported.
int load_sc(int *p) { return __atomic_load_n(p, 5); }
int load_relaxed(int *p) { return __atomic_load_n(p, 0); }
int load_order(int *p, int mo) { return __atomic_load_n(p, mo); }
bool test_and_set(bool *p) { return __atomic_test_and_set(p, 5); }
int fetch_max(int *p) { return __atomic_fetch_max(p, 1, 5); }
void generic_store(int *p, int *v) { __atomic_store(p, v, 5); }

// implicit destructor calls.
struct D { ~D() { asm("nop"); } };
void dtor_local() { D d; }

// a by-value class flowing as a prvalue.
struct VB {};
struct B : virtual VB { int a; };
B mk();
void use(B);
void prvalue() { use(mk()); }

// a conversion to a non-virtual base of a class with a virtual base: each
// step has a static offset (SkyLabsAI/BRiCk#513).
struct NB { int n; };
struct LN : virtual VB, NB { int l; };
int to_nonvirtual_base(LN &x) { NB &b = x; return b.n; }

// a call to a member of a virtual base converts to the virtual base
// (SkyLabsAI/BRiCk#514).
struct VO { int v; bool ok() const { return v != 0; } };
struct LO : virtual VO { int l; };
bool to_virtual_base(LO &x) { return x.ok(); }

// declaration only.
int ext(int);

// [setjmp] returns twice.
typedef long jmp_buf_t[8];
extern "C" int _setjmp(jmp_buf_t);
jmp_buf_t jb;
int calls_setjmp() { if (_setjmp(jb)) return 1; return 0; }

// pointers to members.
struct S { int x; int m() { return x; } };
int dot_member(S &s, int S::*pm) { return s.*pm; }
int arrow_member(S *s, int S::*pm) { return s->*pm; }
int call_member(S &s, int (S::*pm)()) { return (s.*pm)(); }

// statement expressions.
int stmt_expr() { return ({ int x = 1; x; }); }

// [offsetof].
struct O { int a; int b; };
unsigned long off() { return __builtin_offsetof(O, b); }

// a label without a [goto].
void label_only() { L: ; }

// a GNU local label: label names are not unique in the function, and the
// [goto] in the inner block targets the inner [L] (the result is 1).
int local_label() {
  { __label__ L; goto L; int x; L: return 1; }
  L: return 2;
}

// flexible array members.
struct M { int n; int d[]; };
int fam(M *m) { return m->d[0]; }

// a GNU local label without an outer label of the same name: unsupported
// for the declaration, but its names are unique.
int local_label_only() {
  { __label__ M; goto M; M: return 1; }
  return 2;
}

// a GNU local label in a template: clang does not mark the instantiated
// labels as local, so cpp2v prints both [L]s, and the report finds the
// duplicate.
template<class T> int local_label_tmpl(T c) {
  { __label__ L; int n = 0;
    L: if (n++) return 1;
    if (c) goto L; }
  L: return 2;
}
int call_local_label_tmpl() { return local_label_tmpl<int>(1); }

// a labeled declaration in a [switch] body: [case 0] skips it, and the
// assignment is to the inner [x] (the result is 7).
int labeled_decl_switch() {
  int x = 7;
  switch (0) { SKIP: int x; case 0: x = 8; }
  return x;
}

// a [switch] body that is not a block.
int braceless(int x) { switch (x) case 1: return 1; return 0; }

// library builtins called as ordinary functions, and a direct builtin.
extern "C" void *memcpy(void *, const void *, unsigned long);
extern "C" unsigned long strlen(const char *);
void lib_memcpy(char *d, const char *s) { memcpy(d, s, 4); }
unsigned long lib_strlen(const char *s) { return strlen(s); }
void direct_memcpy(char *d, const char *s) { __builtin_memcpy(d, s, 4); }
// Direct builtin calls remain unsupported when they have no semantics.
int direct_undeclared(const char *a, const char *b) { return __builtin_strcmp(a, b); }

// an unused defaulted member that cpp2v does not elaborate.
struct P { P() {} P(const P &) = default; int x; };

// an unsupported type behind a pointer.
void long_double_ptr(long double *p) { (void)p; }

// a parameter of an unnamed struct type: the name mentions [?record].
struct { int a; } *anon_p;
void anon_ptr(decltype(anon_p) p) { (void)p; }

// a default member initializer without semantics.
struct NS { int v = 0 ? 1 : throw 0; int get() const { return 42; } };
int ns_get(NS *n) { return n->get(); }

// unevaluated operands.
unsigned long sizeof_expr(S &s) { return sizeof(s.*(&S::x)); }

// a typedef of a variably modified type: its bound is evaluated (the
// result is 1), which cpp2v prints as a declaration.
int vla_typedef() { int x = 0; typedef int A[(x = 1)]; return x; }

// a condition variable of a variably modified type evaluates its bound
// too (the result is 1), and a condition has no place for the bound.
int vla_condition() { int x = 0; if (int ( *p)[(x = 1)] = nullptr) return 7; return x; }
}}.

Definition show (e : supported.report.entry) :=
  (supported.report.resolved e, supported.report.status e,
   supported.report.unsupported e, supported.report.partial e,
   List.map fst (supported.report.blocked_by e),
   supported.report.unsupported_refs e).

Eval vm_compute in List.map show (supported.report.run source
  [ "va(__builtin_va_list)"; "get_tls()"
  ; "load_sc(int*)"; "load_relaxed(int*)"; "load_order(int*, int)"
  ; "test_and_set(bool*)"; "fetch_max(int*)"; "generic_store(int*, int*)"
  ; "dtor_local()"; "prvalue()"; "to_nonvirtual_base(LN&)"; "to_virtual_base(LO&)"; "ext(int)"; "calls_setjmp()"
  ; "dot_member(S&, int S::*)"; "arrow_member(S*, int S::*)"; "call_member(S&, int (S::*)())"
  ; "stmt_expr()"; "off()"; "label_only()"; "local_label()"; "local_label_only()"; "local_label_tmpl<int>(int)"; "labeled_decl_switch()"; "fam(M*)"; "braceless(int)"
  ; "lib_memcpy(char*, const char*)"; "lib_strlen(const char*)"; "direct_memcpy(char*, const char*)"
  ; "direct_undeclared(const char*, const char*)"
  ; "P::P(const P&)"; "long_double_ptr(long double*)"; "anon_ptr(?record*)"
  ; "long_double_ptr(?Builtin long double*)"; "long_double_ptr(long double&)"; "ns_get(NS*)"
  ; "sizeof_expr(S&)"; "vla_typedef()"; "vla_condition()" ]%pstring).

(** Every non-template entity. *)
Eval vm_compute in
  List.map (fun e => (supported.report.resolved e, supported.report.status e))
    (supported.report.all source).
