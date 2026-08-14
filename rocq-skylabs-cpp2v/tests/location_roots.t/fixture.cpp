struct Self;
typedef struct Self Self;
struct Self {
  int field;
};

struct Ordinary {
  int field;
  static int twice(int value) { return value + value; }
};

enum class Kind { Value = 4 };

template <typename T = int> struct Box {
  T value;
  T get() const { return value; }
};

template <typename T> T identity(T value) { return value; }

int selected(int value);
int selected(int value) { return value; }

int use_templates() {
  Box<> box{3};
  return identity(box.get());
}
