(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.syntax.supported.

(** * [supported.report]: one case per status and per failure *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
struct Bits { int a : 3; };
struct HasBits { Bits b; };
struct Node { Node *next; Bits *bits; };
union U { int i; char c; };
struct Anon { union { int x; char y; }; Anon() : x(1) {} };
struct Base { virtual ~Base(); };
struct Derived : Base {};

int by_value(Bits b) { return b.a; }
int by_pointer(Bits *b) { return b == nullptr; }
int through_field(HasBits *h) { return h->b.a; }
int linked(Node n) { return n.next == nullptr; }
int static_local() { static int x = 0; return x; }
int calls_static_local() { return static_local(); }
int use_union(U u) { u.c = 1; return u.i; }
int arrow_union(U *u) { u->c = 1; return 0; }
int arrow_bits(Bits *b) { return b->a; }
int take_bits(Bits b) { return b.a; }
void address_only() { auto p = &take_bits; (void)p; }
int call_through(Bits *b) { auto p = &take_bits; return p( *b); }
int read_volatile(volatile int *p) { return *p; }
void volatile_local() { volatile int x = 0; (void)x; }
bool dyn(Base *b) { return dynamic_cast<Derived *>(b) != nullptr; }
void inline_asm() { asm("nop"); }
bool cas_ptr(int **p, int **e, int *d) {
  return __atomic_compare_exchange_n(p, e, d, false, 5, 5);
}
bool cas_int(int *p, int *e, int d) {
  return __atomic_compare_exchange_n(p, e, d, false, 5, 5);
}
int overloaded(int x) { return x; }
int overloaded(long x) { return (int)x; }
int unknown_builtin(unsigned x) { return __builtin_popcount(x); }
long known_builtin(long x) { return __builtin_expect(x, 0); }
int flat_switch(int x) { switch (x) { case 0: return 1; default: return 0; } }
int nested_case(int x) { switch (x) { case 0: { case 1: return 1; } default: return 0; } }
int case_after_decl(int x) { switch (x) { case 0: int y; y = 1; return y; case 1: return 1; } return 0; }
}}.

Eval vm_compute in supported.report.run source
  [ "by_value(Bits)"; "by_pointer(Bits*)"; "through_field(HasBits*)"; "linked(Node)"
  ; "static_local()"; "calls_static_local()"; "use_union(U)"; "arrow_union(U*)"; "arrow_bits(Bits*)"; "address_only()"; "call_through(Bits*)"; "read_volatile(volatile int*)"
  ; "volatile_local()"; "dyn(Base*)"; "inline_asm()"; "cas_ptr(int**, int**, int*)"
  ; "cas_int(int*, int*, int)"; "overloaded(int)"; "overloaded(long)"
  ; "unknown_builtin(unsigned int)"; "known_builtin(long)"; "flat_switch(int)"
  ; "nested_case(int)"; "case_after_decl(int)"
  ; "Anon::Anon()"; "Bits"; "HasBits"; "Node"; "U"; "missing()" ]%pstring.

(** [check] keeps only [Unsupported] gaps. *)
Eval vm_compute in supported.check.translation_unit source.

(** * The semantics gets stuck where [supported] fails

    Statements are cut short: these listings guard against rules being added or
    removed, not against their exact shape. *)
Set Printing Depth 5.

(** Every [UNSUPPORTED] in the semantics. A new one may need a [Fail] in
    [supported.v]. *)
Search UNSUPPORTED.

(** No rule: inline assembly, [dynamic_cast], lvalue bitcasts, unsupported casts. *)
Search Sasm -"_ind" -"_rec" -"_rect" -"_sind".
Search Cdynamic -"_ind" -"_rec" -"_rect" -"_sind".
Search Clvaluebitcast -"_ind" -"_rec" -"_rect" -"_sind".
Search Cunsupported -"_ind" -"_rec" -"_rect" -"_sind".

(** Nothing establishes [static_initialized], which static locals need. *)
Search static_initialized.

(** Compare-exchange has rules for integers and booleans only. *)
Search "compare_exchange".

(** Changing a union's active member has no rule. *)
Locate union_change.

(** Each remaining [Gap Unsupported] in [supported.v] mirrors one of these. *)
Section stuck.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  (** [Defaulted] bodies: methods and constructors, not destructors. [report]
      fails a queried one; others are unused, as cpp2v elaborates used ones. *)
  Example defaulted_method (m : Method) args Q :
    m.(m_body) = Some Defaulted ->
    wp_method tu m args Q = UNSUPPORTED "wp_method: defaulted methods"%bs.
  Proof. rewrite wp_method.unlock /=. by case: (m_body m) => [[]|]. Qed.

  Example defaulted_ctor (c : Ctor) args Q :
    c.(c_body) = Some Defaulted ->
    wp_ctor tu c args Q = UNSUPPORTED "wp_ctor: defaulted constructors"%bs.
  Proof. rewrite wp_ctor.unlock /=. by case: (c_body c) => [[]|]. Qed.

  (** Indirect member initialization (members of anonymous structs/unions). *)
  Example indirect_init ρ cls this (m : Member) ms x path f e Q :
    wpi_members tu ρ cls this
      [{| init_path := InitIndirect ((m.(mem_name), x) :: path) f; init_init := e |}]
      (m :: ms) Q
    ⊢ False.
  Proof. rewrite /= bool_decide_true //. apply UNSUPPORTED_elim. Qed.

  (** [switch] bodies that [walk.switch_cases] rejects. *)
  Lemma switch_cases_stuck Ldef b :
    walk.switch_cases b = false -> wp_switch_block Ldef b = None.
  Proof.
    elim: b Ldef => [//|s b IH] Ldef.
    destruct s; cbn [walk.switch_cases wp_switch_block]; try destruct Ldef; move=> H.
    all: try by rewrite IH.
    all: try by rewrite ?H.
    all: case_match eqn:Hc; last done.
    all: apply IH; simpl in *; by rewrite ?Hc in H.
  Qed.

  (** Volatile objects cannot be initialized. *)
  Example volatile_default_init ty p Q :
    default_initialize tu (Tvolatile ty) p Q
    -|- |={⊤}=> UNSUPPORTED "default initialize volatile"%pstring.
  Proof. by rewrite default_initialize.unlock. Qed.
End stuck.
