union BitUnion {
  unsigned bits : 1;
};

struct Base {};
struct WithBase : Base {
  unsigned bits : 1;
};

struct WithVirtual {
  unsigned bits : 1;
  virtual void method();
};

struct WithVirtualBase : virtual Base {
  unsigned bits : 1;
};

struct __attribute__((packed)) PackedBits {
  unsigned bits : 1;
  int unaligned;
};

// Record alignment is sufficient; only the ordinary field offset is invalid.
struct __attribute__((packed, aligned(4))) PackedOffset {
  unsigned bits : 1;
  unsigned unaligned;
};
static_assert(sizeof(PackedOffset) == 8 && alignof(PackedOffset) == 4);
static_assert(__builtin_offsetof(PackedOffset, unaligned) == 1);

struct __attribute__((packed)) PackedPlain {
  char byte;
  int unaligned;
};

template <unsigned Width> struct DependentBits {
  unsigned bits : Width;
};

template <class T> struct DependentType {
  T bits : 1;
};
