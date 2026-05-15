// Empty aggregates

struct s { };
union u { };
enum e { };
enum class ec { };

enum test_constants { A = 0, B, C };

// Functions with incomplete argument types can be declared.
struct i_s;
union i_u;
//enum i_e; // compile error!
enum class i_ec;

i_s f(i_s x);
i_u f(i_u x);
//i_e f(i_e x);
i_ec f(i_ec x);

struct Cl;
Cl* foo();
int foo_caller() {
  Cl* x = foo();
  return 0;
}

struct List {
  struct List* next;
  int data;
};
