struct C {
  const   int x{0};
  mutable int y{0};
  int         z{0};
};
struct D {
          C c;
  const   C cc;
  mutable C mc;
};

void f() {
        D d{};
  const D cd{};

  d.c.y = 1;
  d.c.z = 1;
  d.cc.y = 1;
  d.mc.y = 1;
  d.mc.z = 1;
  
  cd.c.y = 1;
  cd.cc.y = 1;
  cd.mc.y = 1;
  cd.mc.z = 1;
}

/*
void illegal() {
  D d{};
  d.c.x = 1; // UB
}
*/
