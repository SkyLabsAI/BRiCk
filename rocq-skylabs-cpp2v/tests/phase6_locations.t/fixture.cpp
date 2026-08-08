struct Self;
typedef struct Self Self;
struct Self {
  int member;
};

extern int equal_duplicate;
extern int equal_duplicate;

int compatible(int value);
int compatible(int value) { return value; }

int nested_value = 42;

template <typename T> struct Box;
template <typename T> struct Box {
  T value;
};
