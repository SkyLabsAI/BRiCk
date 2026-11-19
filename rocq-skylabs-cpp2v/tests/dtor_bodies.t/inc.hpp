// Destructors the header never uses. cpp2v prints them as [Some Defaulted],
// whether it elaborates them (the default) or not ([--no-elaborate]).
struct M { ~M(); };                 // non-trivial, declared only
struct A { M m; };                  // implicit destructor, non-trivial member
struct B { M m; ~B() = default; };  // explicitly defaulted destructor
struct T { int x; };                // trivial implicit destructor
