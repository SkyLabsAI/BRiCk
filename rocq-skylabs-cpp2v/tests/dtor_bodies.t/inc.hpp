// Destructors the header never uses. cpp2v elaborates them to
// [Some (CompilerProvided _)] by default, and leaves them [Some Defaulted]
// under [--no-elaborate].
struct M { ~M(); };                 // non-trivial, declared only
struct A { M m; };                  // implicit destructor, non-trivial member
struct B { M m; ~B() = default; };  // explicitly defaulted destructor
struct T { int x; };                // trivial implicit destructor
