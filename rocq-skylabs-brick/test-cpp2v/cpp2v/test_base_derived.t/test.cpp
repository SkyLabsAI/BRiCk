struct A {};
struct B : A {};
struct C : A {};
struct D : B , C {};
struct E : D {};
struct F : E {};

void test_derived_to_base() {
  F e;
  (void) (C&)e;
  (void) (B&)e;
  (void) (A&)(B&)e;

  (void) (C&&)static_cast<F&&>(e);
  (void) (B&&)static_cast<F&&>(e);
  (void) (A&&)(B&&)static_cast<F&&>(e);

  (void) (C*)&e;
  (void) (B*)&e;
  (void) (A*)(B*)&e;

  (void) (const C*)&e;
  (void) (const B*)&e;
  (void) (const A*)(B*)&e;
}

void test_base_to_derived(B& a) {
  (void) (F&)a;
  (void) (B&)a;
  (void) (D&)a;

  (void) (F&&)static_cast<B&&>(a);
  (void) (B&&)static_cast<B&&>(a);
  (void) (D&&)static_cast<B&&>(a);

  (void) (F*)&a;
  (void) (B*)&a;
  (void) (D*)&a;

  (void) (const F*)&a;
  (void) (const B*)&a;
  (void) (const D*)&a;
}
