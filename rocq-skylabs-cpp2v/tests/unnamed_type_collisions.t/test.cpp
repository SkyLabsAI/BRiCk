/*
 * Distinct unnamed types whose invented names would coincide.
 * cpp2v must give each its own name (and the generated translation unit must
 * have no duplicates).
 */

// Two unnamed member structs with the same first field ([Nrecord_by_field]).
struct H {
  struct { int a; int b; } *p1;
  struct { long a; long b; long c; } *p2;
};

// Two unnamed local structs named after the same variable ([Nby_first_decl]).
void records() {
  { struct { int a; int b; } x = {1, 0}; (void)x; }
  { struct { int b; int a; } x = {0, 1}; (void)x; }
}

// Two unnamed local enums with the same first enumerator
// ([Nenum_by_enumerator]); each reference must find its own constant.
int enums() {
  int r;
  { enum { A = 1 }; r = A; }
  { enum { A = 0 }; r += A; }
  return r;
}

// An unnamed record and an unnamed enum both named after a child [K]
// ([Nrecord_by_field] and [Nenum_by_enumerator] share [Nfirst_child]).
void mixed() {
  struct { int K; } *p = nullptr;
  (void)p;
  enum { K };
  (void)K;
}

// Typedef names for anonymous local records.
void typedefs() {
  { typedef struct { int a; } S; S x; (void)x; }
  { typedef struct { long a; } S; S y; (void)y; }
}
