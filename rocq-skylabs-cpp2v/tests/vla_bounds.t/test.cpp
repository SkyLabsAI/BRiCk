// Declarations of variably modified types (GNU variable-length arrays in
// C++). Clang evaluates the array bounds where the type is declared.
struct Tmp { int n; Tmp(int); ~Tmp(); };
struct Triv { int n; };
Triv mk();
int dflt(int = 3);
struct S0 { int x; };

// Typedefs and alias declarations: the bounds, outermost first.
void td_2d(int a, int b) { typedef int A[a][b]; }
void td_ptr(int a) { typedef int (*P)[a]; }
void td_ref(int a) { typedef int (&R)[a]; }
void td_const_outer(int a) { typedef int A[3][a]; }
void td_array_of_ptr(int a, int b) { typedef int (*A[a])[b]; }
void td_declarators(int a, int b, int c) { typedef int A[a], B[b], (*C)[c]; }
void td_alias(int a, int b) { using A = int[a][b]; }
void td_paren(int a) { typedef int ((*B))[a]; }
void td_effect(int a) { typedef int A[(a = 1)]; }
void td_sequenced(int a) { typedef int A[a++], B[a++]; }
void td_init(int a) { if (typedef int A[a]; a) return; }
// A typedef of a variably modified typedef evaluates no bound again.
void td_of_td(int a, int b) { typedef int A[a]; typedef A B; using C = B *; typedef A D[b]; }
// Nothing to evaluate.
void td_fn_param(int a) { typedef int F(int x[a]); }
void td_plain() { typedef int A[3]; }
// Unsupported forms.
void td_typeof(int a) { typedef __typeof__(int[a]) X; }
void td_typeof_expr(int a) { typedef int A[a]; typedef __typeof__(*(A *)nullptr) Q; }
void td_decltype(int a) { typedef int A[a]; typedef decltype((A *)nullptr) Q; }
void td_fn_ret(int a) { typedef int (*F(void))[a]; }
void td_atomic(int a) { typedef _Atomic(int (*)[a]) T; }
void td_memptr(int a) { typedef int (*S0::*PM)[a]; }
void td_tmp(int a) { typedef int A[Tmp(a).n]; }
void td_triv() { typedef int A[mk().n]; }
void td_dflt() { typedef int A[dflt()]; }
// The bounds of one declarator are unsequenced.
void td_unsequenced(int a) { typedef int A[a++][a]; }
