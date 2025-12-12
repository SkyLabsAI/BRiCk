void test() {
  using T = int;
  { using T = char;
    { struct T { int x; }; T z;
      /* Check that renaming [T] in the generated AST preserves the binding structure */
      (void) z.x;
    }
    { union T { char c; }; T z; /* Ditto */ (void) z.c; }
  }
  { using T = long long; }
}
