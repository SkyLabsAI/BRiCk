
void foo (int * const x) {

  int * i = x;

  int const * j = x;

  int * const k = x;

  int const * const l = x;

  i = i;
  //i = j; discards qualifiers
  i = k;
  //i = l; discards qualifiers

  j = i;
  j = j;
  j = k;
  j = l;


  *i = *i;
  *i = *j;
  *i = *k;
  *i = *l;

  *k = *i;
  *k = *j;
  *k = *k;
  *k = *l;
}

void
bar() {

  int x{0};

  foo(&x);

}


int foo1(int const * p) { return *p; }

void bar1() {
  int x{0};
  foo1(&x);
}
