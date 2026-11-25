/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 *
 * SPDX-License-Identifier: MIT-0
 */

typedef long long v4di __attribute__((__vector_size__(32)));
typedef long long v4di_u __attribute__((__vector_size__(32), __aligned__(1)));
using v16qi_u __attribute__((__aligned__(1))) = char __attribute__((__vector_size__(16)));

// Qualified vector typedefs with alignment overrides (finding 1).
typedef v4di_u const cu32 __attribute__((__aligned__(32)));
typedef v4di const cv1 __attribute__((__aligned__(1)));

// Padded extended vector (finding 2) and GNU vs. ext_vector overload (finding 5).
typedef float f3_ext __attribute__((__ext_vector_type__(3)));
typedef float f4_ext __attribute__((__ext_vector_type__(4)));
typedef float f4_gnu __attribute__((__vector_size__(16)));

// Over-aligned vector typedef with align > sizeof (finding 3).
typedef int v4si __attribute__((__vector_size__(16)));
typedef v4si v4si_overaligned __attribute__((__aligned__(32)));

static_assert(sizeof(v4di) == 32 && alignof(v4di) == 32, "");
static_assert(sizeof(v4di_u) == 32 && alignof(v4di_u) == 1, "");
static_assert(sizeof(v16qi_u) == 16 && alignof(v16qi_u) == 1, "");
static_assert(sizeof(cu32) == 32 && alignof(cu32) == 32, "");
static_assert(sizeof(cv1) == 32 && alignof(cv1) == 1, "");
static_assert(sizeof(f3_ext) == 16 && alignof(f3_ext) == 16, "");
static_assert(sizeof(v4si_overaligned) == 16 && alignof(v4si_overaligned) == 32, "");

v4di id_vec(v4di const x) {
    return x;
}

v4di_u const *as_unaligned_vec(unsigned char const *p) {
    return reinterpret_cast<v4di_u const *>(p);
}

v16qi_u const *as_unaligned_vec16(char const *p) {
    return reinterpret_cast<v16qi_u const *>(p);
}

unsigned long align_cu32() { return alignof(cu32); }
unsigned long align_cv1() { return alignof(cv1); }

// Aligned/unaligned typedef redeclaration must share one canonical symbol name (finding 4).
void same_vec_fn(v4di *p);
void call_before_redecl(v4di *p) { same_vec_fn(p); }
void same_vec_fn(v4di_u *p) {}

// Declaration-only redeclaration must also share one canonical symbol name (finding 4).
void same_vec_fn_decl_only(v4di *p);
void same_vec_fn_decl_only(v4di_u *p);
void call_after_redecl(v4di_u *p) { same_vec_fn_decl_only(p); }

// GNU vector and Clang ext_vector_type overloads must not collide (finding 5).
int overload_vec(f4_gnu x) { return 1; }
int overload_vec(f4_ext x) { return 2; }
