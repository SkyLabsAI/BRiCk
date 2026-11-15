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
    on code whose verdict used to be wrong. *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
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

// flexible array members.
struct M { int n; int d[]; };
int fam(M *m) { return m->d[0]; }

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

// a default member initializer without semantics.
struct NS { int v = 0 ? 1 : throw 0; int get() const { return 42; } };
int ns_get(NS *n) { return n->get(); }

// unevaluated operands.
unsigned long sizeof_expr(S &s) { return sizeof(s.*(&S::x)); }
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
  ; "dtor_local()"; "prvalue()"; "ext(int)"; "calls_setjmp()"
  ; "dot_member(S&, int S::*)"; "arrow_member(S*, int S::*)"; "call_member(S&, int (S::*)())"
  ; "stmt_expr()"; "off()"; "label_only()"; "fam(M*)"; "braceless(int)"
  ; "lib_memcpy(char*, const char*)"; "lib_strlen(const char*)"; "direct_memcpy(char*, const char*)"
  ; "direct_undeclared(const char*, const char*)"
  ; "P::P(const P&)"; "long_double_ptr(long double*)"; "ns_get(NS*)"
  ; "sizeof_expr(S&)" ]%pstring).

(** Every non-template entity. *)
Eval vm_compute in
  List.map (fun e => (supported.report.resolved e, supported.report.status e))
    (supported.report.all source).
